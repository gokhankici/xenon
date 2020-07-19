-- {-# OPTIONS_GHC -Wno-unused-binds #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE StrictData          #-}

module Main (main) where

import           TestData

import qualified Iodine.IodineArgs as IA
import qualified Iodine.Runner as R

import           Control.Exception
import           Control.Lens hiding (simple, (<.>))
import           Control.Monad
import           Data.Foldable
import           Data.Maybe
import           GHC.Generics hiding (moduleName, to)
import           GHC.IO.Handle
import           System.Console.CmdArgs.Explicit
import           System.Environment
import           System.Exit
import           System.IO
import           Test.Hspec
import           Test.Hspec.Core.Runner
import           Test.Hspec.Core.Spec
import           Text.Printf

data TestArgs =
  TestArgs { _verbose      :: Bool
           , _help         :: Bool
           , _iodineArgs   :: [String]
           , _hspecArgs    :: [String] -- | rest of the positional arguments
           , _runAbduction :: Bool
           , _dryRun       :: Bool
           }
  deriving (Generic, Show)

makeLenses ''TestArgs

--------------------------------------------------------------------------------
runTestTree :: TestArgs -> IA.IodineArgs -> TestTree -> Spec
--------------------------------------------------------------------------------
runTestTree ta templateIA = \case
  TestCollection name tests ->
    describe name $ traverse_ (runTestTree ta templateIA) tests
  SingleTest u@UnitTest{..} ->
    it testName $ do
    ia <- getIodineArgs ta u templateIA
    if ta ^. dryRun
      then printf "./iodine %s %s\n" (IA.fileName ia) (IA.annotFile ia)
      else withSilence $ R.runner ia `shouldReturn` expected
    where
      expected    = testType == Succ
      withSilence = if ta ^. verbose then id else silence

getIodineArgs :: TestArgs -> UnitTest -> IA.IodineArgs -> IO IA.IodineArgs
getIodineArgs ta UnitTest{..} templateIA =
  IA.normalizeIodineArgs $
  templateIA
  { IA.fileName   = verilogFile
  , IA.annotFile  = fromMaybe (IA.defaultAnnotFile verilogFile) annotFile
  , IA.noSave     = True
  , IA.verbosity  = if ta ^. verbose then IA.Loud else IA.Normal
  }

spec :: TestArgs -> IA.IodineArgs -> Spec
spec ta templateIA = sequential $ traverse_ (runTestTree ta templateIA) allTests

silence :: IO a -> IO a
silence action = withFile "/dev/null" AppendMode prepareAndRun
  where
    handles = [stdout, stderr]
    prepareAndRun tmpHandle = go handles
      where
        go [] = action
        go hs = goBracket go tmpHandle hs

    goBracket _ _ [] = error "not possible?"
    goBracket go tmpHandle (h:hs) = do
      buffering <- hGetBuffering h
      let redirect = do
            old <- hDuplicate h
            hDuplicateTo tmpHandle h
            return old
          restore old = do
            hDuplicateTo old h
            hSetBuffering h buffering
            hClose old
      bracket redirect restore (\_ -> go hs)

-- -----------------------------------------------------------------------------
-- Argument Parsing
-- -----------------------------------------------------------------------------

testArgs :: Mode TestArgs
testArgs = mode programName def detailsText (flagArg argUpd "HSPEC_ARG") flags
  where
    flags = [ flagReq ["iodine"] (\s -> Right . over iodineArgs (++ words s)) "IODINE_ARG"
              "This is passed to the Iodine script directly."
            , flagNone ["a", "abduction"] (set runAbduction True)
              "Only run the abduction tests, otherwise they are disabled."
            , flagNone ["v", "verbose"] (set verbose True)
              "Display both stdout & stderr of a test."
            , flagNone ["d", "dry-run"] (set dryRun True)
              "Print the calls to Iodine"
            , flagNone ["h", "help"] (set help True)
              "Displays this help message."
            ]

    argUpd s = Right . over hspecArgs (++ [s])

    programName = "iodine-test"
    detailsText = unlines [ "Runs the benchmarks."
                          , "The positional arguments (e.g. after --) are passed into hspec."
                          ]

    def = TestArgs { _verbose      = False
                   , _help         = False
                   , _iodineArgs   = []
                   , _hspecArgs    = []
                   , _runAbduction = False
                   , _dryRun       = False
                   }

parseOpts :: IO TestArgs
parseOpts = do
  res <-  fmap post . process testArgs <$> getArgs
  case res of
    Left errMsg -> error errMsg
    Right opts  -> do
      when (opts^.help) $ do
        print $ helpText [] HelpFormatDefault testArgs
        exitSuccess
      return opts
  where
    post o =
      if o ^. runAbduction
      then over hspecArgs  (++ ["--match", '/':abductionRoot]) .
           over iodineArgs (++ ["--abduction"]) .
           set  verbose    True $
           o
      else over hspecArgs (++ ["--skip",  '/':abductionRoot]) o

--------------------------------------------------------------------------------
main :: IO ()
--------------------------------------------------------------------------------
main = do
  opts <- parseOpts

  -- if no Iodine argument is given, use the following default ones
  let updateDef va =
        if null $  opts ^. iodineArgs
        then va { IA.noSave     = True
                , IA.noFPOutput = view (verbose . to not) opts
                }
        else va

  -- hack: set the required first two positional arguments to empty list
  templateIA <- updateDef . invalidate <$> IA.parseArgsWithError ("" : "" : opts ^. iodineArgs)

  readConfig defaultConfig (opts^.hspecArgs)
    >>= withArgs [] . runSpec (spec opts templateIA)
    >>= evaluateSummary
  where
    invalidate va = va { IA.fileName   = undefined
                       , IA.annotFile  = undefined
                       , IA.benchmarkMode = True
                       }
