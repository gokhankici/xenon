{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# OPTIONS_GHC -fno-cse #-}

module Iodine.IodineArgs
  ( IodineArgs(..)
  , defaultIodineArgs
  , parseArgs
  , parseArgsWithError
  , defaultAnnotFile
  ) where

import Control.Monad
import Data.List
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Text
import System.Console.CmdArgs.Verbosity
import System.Exit
import System.FilePath

-- import System.Environment

-- -----------------------------------------------------------------------------
-- Argument Parsing
-- -----------------------------------------------------------------------------
{- |
@
iodine v2.0, (C) Rami Gokhan Kici 2020

Verifies whether the given Verilog file runs in constant time under the given
assumptions.

First positional argument is the verilog file to analyze.
Second positional argument is the JSON file that contains the annotations.

iodine [OPTIONS] VERILOG-FILE ANNOTATION-FILE

     --iverilog-dir=DIR  path of the iverilog-parser directory
     --print-ir          just run the verilog parser
     --vcgen             just generate the .fq file
     --no-save           do not save the fq file
     --no-fp-output      disable the output from fixpoint
     --abduction         run abduction algorithm
     --no-sanity-check   do not run the sanity check step (for benchmarking)
  -v --verbose           Loud verbosity
  -q --quiet             Quiet verbosity
-}
data IodineArgs =
  IodineArgs { fileName    :: FilePath -- this is used for both the Verilog and IR file
             , annotFile   :: FilePath
             , iverilogDir :: FilePath
             , printIR     :: Bool
             , onlyVCGen   :: Bool
             , noSave      :: Bool
             , noFPOutput  :: Bool
             , abduction   :: Bool
             , verbose     :: Bool
             , moduleName  :: String
             , noSanity    :: Bool
             , delta       :: Bool
             }
  deriving (Show)

defaultIodineArgs :: IodineArgs
defaultIodineArgs =
  IodineArgs { fileName    = ""
             , annotFile   = ""
             , iverilogDir = "iverilog-parser"
             , printIR     = False
             , onlyVCGen   = False
             , noSave      = False
             , noFPOutput  = False
             , abduction   = False
             , verbose     = False
             , moduleName  = ""
             , noSanity    = False
             , delta       = False
             }

programName :: String
programName = "iodine"

iodineMode :: Mode IodineArgs
iodineMode =
  iodineModeWithoutPositional
  { modeArgs = (parsePositionalArgs, Nothing) }
  where
    iodineModeWithoutPositional =
      mode programName defaultIodineArgs "" undefined parseFlags

iodineHelpText :: [String]
iodineHelpText =
  [ programName ++ " v2.0, (C) Rami Gokhan Kici 2020"
  , ""
  , "Verifies whether the given Verilog file runs in constant time under the given assumptions."
  , ""
  , "First positional argument is the verilog file to analyze."
  , "Second positional argument is the JSON file that contains the annotations."
  ]

parsePositionalArgs :: [Arg IodineArgs]
parsePositionalArgs =
  [ Arg { argValue   = \f ia -> Right ia { fileName = f }
        , argType    = "VERILOG-FILE"
        , argRequire = True
        }
  , Arg { argValue   = \f ia -> Right ia { annotFile = f }
        , argType    = "ANNOTATION-FILE"
        , argRequire = True
        }
  ]

parseFlags :: [Flag IodineArgs]
parseFlags =
  [ flagReq ["iverilog-dir"]
    (\d ia -> Right ia { iverilogDir = d })
    "DIR"
    "path of the iverilog-parser directory"
  , flagNone ["print-ir"]
    (\ia -> ia { printIR = True })
    "just run the verilog parser"
  , flagNone ["vcgen"]
    (\ia -> ia { onlyVCGen = True })
    "just generate the .fq file"
  , flagNone ["no-save"]
    (\ia -> ia { noSave = True })
    "do not save the fq file"
  , flagNone ["no-fp-output"]
    (\ia -> ia { noFPOutput = True })
    "disable the output from fixpoint"
  , flagNone ["abduction"]
    (\ia -> ia { abduction = True })
    "run abduction algorithm"
  , flagNone ["no-sanity-check"]
    (\ia -> ia { noSanity = True })
    "do not run the sanity check step (for benchmarking)"
  , flagNone ["delta"]
    (\ia -> ia { delta = True })
    "run fixpoint in delta debugging mode"
  ]
  ++ flagsVerbosity (\v ia -> ia { verbose = v == Loud })

parseArgs :: [String] -> Either String IodineArgs
parseArgs = process iodineMode

isHelpNeeded :: [String] -> (Bool, [String])
isHelpNeeded args = if null args then (True, []) else (not $ null helpArgs, rest)
  where
    (helpArgs, rest) = partition (`elem` ["-h", "--help"]) args

parseArgsWithError :: [String] -> IO IodineArgs
parseArgsWithError args = do
  let (isHelp, args') = isHelpNeeded args
  when isHelp printHelp
  processValueIO iodineMode args'

printHelp :: IO ()
printHelp = do
  let hf = HelpFormatDefault
      tf = defaultWrap
  putStrLn $
    showText tf $
    helpText iodineHelpText hf iodineMode
  exitSuccess

defaultAnnotFile :: FilePath -> FilePath
defaultAnnotFile verilogFile =
  let dir  = takeDirectory verilogFile
      name = dropExtension $ takeBaseName verilogFile
  in  dir </> "annot-" ++ name <.> "json"

