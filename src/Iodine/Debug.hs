{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Debug where

import           Iodine.Analyze.ModuleSummary
import           Iodine.IodineArgs
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Language.IRParser
import           Iodine.Runner (generateIR, readIRFile)
import           Iodine.Transform.Merge
import           Iodine.Transform.Normalize
import           Iodine.Transform.VariableRename
import           Iodine.Types

import qualified Control.Exception as E
import           Control.Monad
import           Data.Foldable
import           Data.Function
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import           Polysemy hiding (run)
import           Polysemy.Error
import           Polysemy.Output
import           Polysemy.Reader
import           Polysemy.Trace
import           System.Directory
import           System.FilePath.Posix
import           System.IO.Error
import           Text.Printf


debugVerilogFile, debugAnnotationFile :: FilePath
debugVerilogFile    = "benchmarks" </> "472-mips-pipelined" </> "mips_pipeline.v"
debugAnnotationFile = commonAnnotationFile debugVerilogFile

debug :: D r => Sem r ()
debug = do
  ModuleSummary{..} <- asks (HM.! "mips_pipeline")
  output $ printGraph threadDependencies show


type ModuleMap = HM.HashMap Id (Module Int)
type G r  = Members '[Error IodineException, Trace, Output String] r
type D r = Members '[ Reader AnnotationFile
                    , Error IodineException
                    , Trace
                    , Reader ModuleMap
                    , Reader SummaryMap
                    , Output String
                    ] r

debugPipeline :: G r => AnnotationFile -> Sem r (L (Module ())) -> Sem r ()
debugPipeline af irReader = do
  (af', ir) <- variableRename af . assignThreadIds <$> irReader
  let irMap = mkModuleMap ir

  runReader af' $ do
    (normalizedIR, _) <-
      (merge ir & runReader irMap)
      >>= normalize
    -- traverse_ (trace . show) normalizedIR
    let normalizedIRMap = mkModuleMap normalizedIR
    moduleSummaries <- createModuleSummaries normalizedIRMap
    debug
      & runReader moduleSummaries
      & runReader normalizedIRMap


run :: IO ()
run = do
  (IodineArgs{..}, af) <- debugArgs >>= generateIR
  irFileContents <- readIRFile fileName
  r <- tryIOError $ removeFile outputFile
  case r of
    Right _ -> return ()
    Left e -> unless (isDoesNotExistError e) $ E.throwIO e
  res <- debugPipeline af (parse (fileName, irFileContents))
    & (if verbose then traceToIO else ignoreTrace)
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
  rest <- traverse makeAbsolute [debugVerilogFile, debugAnnotationFile]
  parseArgsWithError $
    [ "--iverilog-dir", ivd
    , "--verbose"
    ] ++ rest


commonAnnotationFile :: FilePath -> FilePath
commonAnnotationFile verilogFile =
  parentDir </> ("annot-" ++ name -<.> "json")
  where
    (parentDir, name) = splitFileName verilogFile

mkModuleMap :: L (Module a) -> HM.HashMap Id (Module a)
mkModuleMap =
  foldl' (\acc m@Module{..} -> HM.insert moduleName m acc) mempty

printGraph :: G.Gr a b -> (Int -> String) -> String
printGraph g nodeLookup = unlines ls
  where
    ls = "digraph iodine {" : edges ++ nodes ++ ["}"]
    edges = mkEdge <$> G.edges g
    nodes = mkNode <$> G.nodes g
    mkEdge (x,y) = printf "%d -> %d;" x y
    mkNode n = printf "%d [label=\"%s\"];" n (nodeLookup n)
