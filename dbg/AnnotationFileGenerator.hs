{-# LANGUAGE TupleSections #-}

module AnnotationFileGenerator
  ( generateAnnotationFile
  )
where

import           Control.Carrier.Error.Either
import           Control.Exception
import           Data.Foldable
import           Data.Maybe
import qualified Data.Text as T
import           Iodine.Analyze.ModuleDependency
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import qualified Iodine.Language.IRParser      as IRP
import           Iodine.Runner (verilogToIR)
import           Iodine.Types
import           System.Directory
import           System.FilePath
import           Control.Lens
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Aeson
import           Data.Bifunctor
import qualified Data.ByteString.Lazy as B


guessIVerilogDir :: FilePath -> IO (Maybe FilePath)
guessIVerilogDir "/" = return Nothing
guessIVerilogDir cwd = do
  let d = cwd </> "iverilog-parser"
  check <- doesDirectoryExist d
  if check
    then return (Just d)
    else guessIVerilogDir $ takeDirectory cwd

generateAnnotationFile :: FilePath -> String -> FilePath -> [String] -> IO ()
generateAnnotationFile filename topModule outputfile includeDirs = do
  iverilogDir <- fromJust <$> (getCurrentDirectory >>= guessIVerilogDir)
  absFilename <- makeAbsolute filename
  irFile <- verilogToIR iverilogDir absFilename topModule includeDirs
  mir <- readFile irFile >>= (runError . IRP.parse . (filename, ))
  let modules = either (\(e :: IodineException) -> throw e)
                       (topsortModules $ T.pack topModule)
                       mir
  let af = AnnotationFile { _afAnnotations = HM.fromList $ (\m -> (moduleName m, mkMA m)) <$> toList modules
                          , _afTopModule   = T.pack topModule
                          , _afIncludeDirs = T.pack <$> includeDirs
                          }
  B.writeFile outputfile $ encode af

  where
    goP acc (Input p)  = first (HS.insert (variableName p)) acc
    goP acc (Output p) = second (HS.insert (variableName p)) acc

    goE acc Star = acc
    goE acc e = acc <> getVariables (eventExpr e)

    mkMA m =
      let (ins0, outs) = foldl' goP (mempty, mempty) (ports m)
          clks = foldl' goE mempty (abEvent <$> alwaysBlocks m)
          ins = ins0 `HS.difference` clks
          addSources = if T.pack topModule == moduleName m
                       then moduleAnnotations .~ (emptyAnnotations & (sources .~ ins) . (sinks .~ outs))
                       else id
      in emptyModuleAnnotations
         & addSources
         . (clocks .~ clks)
