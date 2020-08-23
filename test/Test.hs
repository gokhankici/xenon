{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE StrictData          #-}

module Main (main) where

import           TestData

import qualified Xenon.XenonArgs as IA
import qualified Xenon.Runner as R
import           Xenon.Language.Annotation

import qualified Language.Fixpoint.Types as FT

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
import           System.Directory
import           System.FilePath
import           System.Process
import qualified Data.ByteString.Lazy as B
import qualified Data.Text as T
import           System.TimeIt (timeItT)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.Map as M
-- import           Debug.Trace


tableTests :: M.Map String String
tableTests = M.fromList
  [ ("mips_pipeline"  , "MIPS")
  , ("yarvi"          , "RISC-V")
  , ("sha256"         , "SHA-256")
  , ("fpu"            , "FPU")
  , ("scarv_cop_palu" , "ALU")
  , ("divider"        , "FPU2")
  , ("ModExp"         , "RSA")
  , ("aes_256"        , "AES-256")
  , ("frv_core"       , "SCARV")
  ]

enableRuns :: Bool
enableRuns = False

runCount :: Int
runCount = 10

data TestArgs =
  TestArgs { _verbose      :: Bool
           , _help         :: Bool
           , _xenonArgs   :: [String]
           , _hspecArgs    :: [String] -- | rest of the positional arguments
           , _runAbduction :: Bool
           , _dryRun       :: Bool
           , _evalTable    :: Bool
           , _consTable    :: Bool
           }
  deriving (Generic, Show)

makeLenses ''TestArgs

--------------------------------------------------------------------------------
runTestTree :: TestArgs -> IA.XenonArgs -> TestTree -> Spec
--------------------------------------------------------------------------------
runTestTree ta templateIA = \case
  TestCollection name tests ->
    describe name $ traverse_ (runTestTree ta templateIA) tests
  SingleTest u@UnitTest{..} ->
    it testName $ do
    ia <- getXenonArgs ta u templateIA
    if ta ^. dryRun
      then printf "./xenon %s %s\n" (IA.fileName ia) (IA.annotFile ia)
      else withSilence $ R.runner ia `shouldReturn` expected
    where
      expected    = testType == Succ
      withSilence = if ta ^. verbose then id else silence

getXenonArgs :: TestArgs -> UnitTest -> IA.XenonArgs -> IO IA.XenonArgs
getXenonArgs ta UnitTest{..} templateIA =
  IA.normalizeXenonArgs $
  templateIA
  { IA.fileName   = verilogFile
  , IA.annotFile  = fromMaybe (IA.defaultAnnotFile verilogFile) annotFile
  , IA.noSave     = True
  , IA.verbosity  = if ta ^. verbose then IA.Loud else IA.Normal
  }

spec :: TestArgs -> IA.XenonArgs -> Spec
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
    flags = [ flagReq ["xenon"] (\s -> Right . over xenonArgs (++ words s)) "XENON_ARG"
              "This is passed to the Xenon script directly."
            , flagNone ["a", "abduction"] (set runAbduction True)
              "Only run the abduction tests, otherwise they are disabled."
            , flagNone ["v", "verbose"] (set verbose True)
              "Display both stdout & stderr of a test."
            , flagNone ["d", "dry-run"] (set dryRun True)
              "Print the calls to Xenon"
            , flagNone ["eval-table"] (set evalTable True)
              "Print the Verilog LOC table"
            , flagNone ["constraint-table"] (set consTable True)
              "Print the Verilog LOC table"
            , flagNone ["h", "help"] (set help True)
              "Displays this help message."
            ]

    argUpd s = Right . over hspecArgs (++ [s])

    programName = "xenon-test"
    detailsText = unlines [ "Runs the benchmarks."
                          , "The positional arguments (e.g. after --) are passed into hspec."
                          ]

    def = TestArgs { _verbose      = False
                   , _help         = False
                   , _xenonArgs   = []
                   , _hspecArgs    = []
                   , _runAbduction = False
                   , _dryRun       = False
                   , _evalTable    = False
                   , _consTable    = False
                   }

parseOpts :: IO TestArgs
parseOpts = do
  res <-  process testArgs <$> getArgs
  case res of
    Left errMsg -> error errMsg
    Right opts  -> do
      when (opts^.help) $ do
        print $ helpText [] HelpFormatDefault testArgs
        exitSuccess
      return opts

--------------------------------------------------------------------------------
main :: IO ()
--------------------------------------------------------------------------------
main = do
  opts <- parseOpts

  -- if no Xenon argument is given, use the following default ones
  let updateDef va =
        if null $  opts ^. xenonArgs
        then va { IA.noSave     = True
                , IA.noFPOutput = view (verbose . to not) opts
                }
        else va

  -- hack: set the required first two positional arguments to empty list
  templateIA <- updateDef . invalidate <$> IA.parseArgsWithError ("" : "" : opts ^. xenonArgs)

  if | opts ^. evalTable -> printSizeTable
     | opts ^. consTable -> for_ benchmarks printConstraintSizes
     | otherwise -> readConfig defaultConfig (opts^.hspecArgs)
                    >>= withArgs [] . runSpec (spec opts templateIA)
                    >>= evaluateSummary
  where
    invalidate va = va { IA.fileName   = undefined
                       , IA.annotFile  = undefined
                       , IA.benchmarkMode = True
                       }

printSizeTable :: IO ()
printSizeTable = do
  printf "%-15s & %4s & %3s & %3s & %8s & %7s \\\\\n"
    "Benchmark" "LOC"
    "#IE" "#AE"
    "CT?"
    "Runtime"
  for_ benchmarks printUnitTest

printUnitTest :: Benchmark -> IO ()
printUnitTest b = do
  (testIA, af) <- mkIA u
  let vf = IA.fileName testIA
      vfDir = takeDirectory vf
      vfName = dropExtension $ takeBaseName vf
      preproc = vfDir </> "" <.> vfName <.> "preproc" <.> "v"
      slnc = if IA.verbosity testIA == IA.Quiet then silence else id
  let tick = if isCT then "\\tickYes" else "\\tickNo"
  R.generateIR testIA
  loc <- (length . lines) <$>
         readProcess ("scripts" </> "remove_comments.sh") [preproc] ""
  results <-
    if enableRuns
      then do let act = timeItT (slnc $ R.runner testIA)
                  acts = replicate runCount act
              (runtimes, rcs) <- unzip <$> sequence acts
              unless (all (== isCT) rcs) $
                error $ printf "%s did not match the expected result" prettyName
              return runtimes
      else return [0]
  let ieCount = annotCount initialEquals instanceInitialEquals af
      aeCount = annotCount alwaysEquals instanceAlwaysEquals af
  printf "%-15s & %4d & %3d & %3d & %8s & %7.2f \\\\\n"
    prettyName loc
    ieCount aeCount
    tick
    (mean results)
  where
    u@UnitTest{..} = benchmarkTest b
    prettyName     = benchmarkName b
    isCT = testType == Succ
    annotCount l1 l2 af =
      let go a = HS.size (a ^. l1) + HS.size (a ^. l2)
      in sum $ (^. moduleAnnotations . to go) <$> HM.elems (af ^. afAnnotations)

printConstraintSizes :: Benchmark -> IO ()
printConstraintSizes (Benchmark u@UnitTest{..} prettyName) = do
  testIA0 <- fst <$> mkIA u
  let testIA = testIA0 { IA.verbosity     = IA.Quiet
                       , IA.noSave        = False
                       , IA.benchmarkMode = False
                       , IA.onlyVCGen     = True
                       }
  (finfo, _) <- R.generateIR testIA >>= uncurry R.computeFInfo
  rc <- silence $ R.runner testIA
  unless rc $ error "expecting vcgen to finish"
  let vf = IA.fileName testIA
      bfqFile =
        takeDirectory vf </>
        ".liquid" </>
        "" <.> (dropExtension $ takeBaseName vf) <.> "pl" <.> "bfq"
  fs <- withFile bfqFile ReadMode hFileSize
  printf "%-15s %3d %10d\n" prettyName (HM.size $ FT.cm finfo) fs

mean :: (Fractional a, Foldable t) => t a -> a
mean ds = sum ds / fromIntegral (length ds)


mkIA :: UnitTest -> IO (IA.XenonArgs, AnnotationFile)
mkIA UnitTest{..} = do
  cwd <- getCurrentDirectory
  let vf = cwd </> verilogFile
      afName = fromMaybe (IA.defaultAnnotFile vf) annotFile
  af <- parseAnnotations <$> B.readFile afName
  let ia = IA.defaultXenonArgs
           { IA.fileName      = vf
           , IA.annotFile     = afName
           , IA.moduleName    = T.unpack $ af ^. afTopModule
           , IA.noSave        = True
           , IA.noFPOutput    = True
           , IA.iverilogDir   = cwd </> "iverilog-parser"
           , IA.benchmarkMode = bm
           , IA.verbosity     = vrb
           }
  return (ia, af)
  where
    enableOutput = False
    bm = not enableOutput
    vrb = if enableOutput then IA.Loud else IA.Quiet

data Benchmark = Benchmark
  { benchmarkTest :: UnitTest
  , benchmarkName :: String
  }

benchmarks :: [Benchmark]
benchmarks =
  [ Benchmark u n
  | u <- us
  , let vfName = dropExtension $ takeBaseName $ verilogFile u
  , n <- toList (M.lookup vfName tableTests)
  ]
  where
    us = testTreeToUnits major ++ testTreeToUnits scarv
