{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Debug where

import           Iodine.Analyze.ModuleSummary
import           Iodine.IodineArgs
import qualified Iodine.IodineArgs as IA
import           Iodine.Language.Annotation
import           Iodine.Language.IR as IR
import           Iodine.Language.IRParser
import           Iodine.Pipeline (normalizeIR)
import           Iodine.Runner (generateIR, readIRFile)
import           Iodine.Transform.Merge
import           Iodine.Transform.Normalize
import           Iodine.Transform.VCGen
import           Iodine.Transform.VariableRename
import           Iodine.Types
import           Iodine.Utils

import qualified Control.Exception as E
import           Control.Lens
import           Control.Monad
import           Data.Bifunctor
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Hashable
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import           Data.Maybe
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Polysemy hiding (run)
import           Polysemy.Error
import           Polysemy.Output
import           Polysemy.Reader
import           Polysemy.State
import qualified Polysemy.Trace as PT
import           System.Directory
import           System.FilePath.Posix
import           System.IO.Error
import           Text.Printf

enableVerbose       = True
debugVerilogFile    = "benchmarks" </> "472-mips-pipelined" </> "mips_pipeline.v"
debugAnnotationFile = commonAnnotationFile debugVerilogFile

allRegisterDependencies :: D r => Id -> Id -> Sem r Ids
allRegisterDependencies mn var = do
  Module{..} <- asks (! mn)
  ModuleSummary{..} <- asks (! mn)
  -- trace' "variables" (toList variables)
  let g = variableDependencies
      toId = (variableDependencyNodeMap !)
      toVar = (invVariableDependencyNodeMap IM.!)
      -- varNo = toId var
  -- trace ("pre of " ++ T.unpack var ++ " " ++ show varNo) (first toVar <$> G.lpre g varNo)
  -- trace ("pre of " ++ T.unpack var) (G.lpre g (toId var))
  let isReg r = Register r `elem` variables
      wl regs _ SQ.Empty = return regs
      wl regs history (n SQ.:<| ns) = -- do
        -- trace' "wl" (regs, history, n, ns)
        if IS.member n history
          then wl regs history ns
          else do
          let history' = IS.insert n history
              ps = SQ.filter (not . (`IS.member` history)) $ toSequence $ G.pre g n
              nv = toVar n
              (regs', ns') =
                if isReg nv
                then (HS.insert nv regs, ns)
                else foldl'
                     (\(rs, vns) vn ->
                        let v = toVar vn
                        in if isReg v
                           then (HS.insert v rs, ns)
                           else (rs, vns SQ.|> vn))
                     (regs, ns)
                     ps
          -- trace' "vn" (toVar n)
          -- trace' "ps" (toVar <$> ps)
          -- trace' "ps'" (toVar <$> G.pre g n)
          wl regs' history' ns'
  let varId  = toId var
      preVarIds = toSequence $ G.pre g varId
  wl mempty mempty preVarIds
  -- regDeps <- wl mempty mempty preVarIds
  -- trace
  --   (printf "register dependencies of %s in module %s" var mn)
  --   regDeps
  -- return regDeps

printThreadDeps :: D r => Sem r ()
printThreadDeps = do
  ModuleSummary{..} <- asks (! "mips_pipeline")
  output $ printGraph threadDependencies show

getCondVars :: L (AlwaysBlock Int) -> Sem r Ids
getCondVars as = execState mempty $ do
  let goStmt = \case
        Block{..} -> traverse_ goStmt blockStmts
        Assignment{..} -> return ()
        IfStmt{..} -> do
          modify (HS.union $ getVariables ifStmtCondition)
          goStmt ifStmtThen
          goStmt ifStmtElse
        Skip{} -> return ()
  traverse_ goStmt (abStmt <$> as)

getMissingInitialEquals :: (D r, Members '[Reader (HM.HashMap Id Ids)] r)
                        => Module Int -> Sem r Ids
getMissingInitialEquals Module{..} = do
  PT.trace $ printf "getMissingInitialEquals - %s" moduleName
  allInitEqs :: Ids <- asks (HM.! moduleName)
  let isInitEq = (`elem` allInitEqs)
  registersThatAffectConditions <-
    fold
    <$> (toSequence <$> getCondVars alwaysBlocks
         >>= traverse (allRegisterDependencies moduleName))
  -- trace "registers that affect conditions" (HS.toList registersThatAffectConditions)
  let missingRegs = HS.filter (not . isInitEq) registersThatAffectConditions
  trace "missing registers" (HS.toList missingRegs)
  return missingRegs

debug2 :: D r => Sem r ()
debug2 = do
  ir <- ask @IRs
  allIEs <- computeAllInitialEqualVars ir
  traverse_ getMissingInitialEquals ir
    & runReader allIEs

debug :: D r => Sem r ()
debug = do
  ModuleSummary{..} <- asks (! "mux3")
  PT.trace $ show portDependencies
  PT.trace $ show isCombinatorial

type IRs = L (Module Int)
type ModuleMap = HM.HashMap Id (Module Int)
type G r  = Members '[Error IodineException, PT.Trace, Output String] r
type D r = ( G r
           , Members '[ Reader AnnotationFile
                      , Reader ModuleMap
                      , Reader SummaryMap
                      , Reader IRs
                      ] r
           )

debugPipeline :: G r => AnnotationFile -> Sem r (L (Module ())) -> IA.IodineArgs -> Sem r ()
debugPipeline af irReader ia = do
  (af', normalizedOutput@(normalizedIR, _)) <- normalizeIR af irReader ia
  runReader af' $ do
    let normalizedIRMap = mkMap IR.moduleName normalizedIR
    moduleSummaries <- createModuleSummaries normalizedIR normalizedIRMap
    (vcgen normalizedOutput >> debug)
      & runReader moduleSummaries
      & runReader normalizedIRMap
      & runReader normalizedIR


run :: IO ()
run = do
  (ia@IodineArgs{..}, af) <- debugArgs >>= generateIR
  irFileContents <- readIRFile fileName
  r <- tryIOError $ removeFile outputFile
  case r of
    Right _ -> return ()
    Left e -> unless (isDoesNotExistError e) $ E.throwIO e
  res <- debugPipeline af (parse (fileName, irFileContents)) ia
    & (if verbose then PT.traceToIO else PT.ignoreTrace)
    & errorToIOFinal
    & runOutputSem (embed . appendFile outputFile)
    & embedToFinal
    & runFinal
  case res of
    Left err -> E.throwIO err
    Right _  -> return ()
  where
    outputFile = "debug-output"


debugArgs :: IO IodineArgs
debugArgs = do
  ivd <- makeAbsolute "iverilog-parser"
  vf  <- makeAbsolute debugVerilogFile
  af  <- makeAbsolute debugAnnotationFile
  return $ defaultIodineArgs
    { fileName    = vf
    , annotFile   = af
    , iverilogDir = ivd
    , verbose     = enableVerbose
    }


commonAnnotationFile :: FilePath -> FilePath
commonAnnotationFile verilogFile =
  parentDir </> ("annot-" ++ name -<.> "json")
  where
    (parentDir, name) = splitFileName verilogFile

(!) :: (Eq k, Hashable k, Show k)
    => HM.HashMap k v -> k -> v
m ! k =
  case HM.lookup k m of
    Nothing -> error $ printf "Could not find %s in %s" (show k) (show $ HM.keys m)
    Just v -> v

trace' :: (Members '[PT.Trace] r, Show a) => String -> a -> Sem r ()
trace' msg a = PT.trace (msg ++ " " ++ show a)
