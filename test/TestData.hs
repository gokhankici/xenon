{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE StrictData          #-}

module TestData where

import qualified Iodine.IodineArgs as IA
import           System.FilePath

data UnitTestType = Succ | Fail deriving (Eq, Show)

data UnitTest =
  UnitTest
  { testName    :: String
  , verilogFile :: FilePath       -- | verilog file contains the top level module
  , annotFile   :: Maybe FilePath -- | JSON file that contains the annotations.
                                  -- Default value is "dir/annot-name.json".
                                  -- where "dir/name.v" is the verilog file
  , testType    :: UnitTestType
  }

-- | default unit test patterns
pattern T :: String -> FilePath -> UnitTest
pattern T testName verilogFile =
  UnitTest { annotFile = Nothing
           , testType  = Succ
           , ..
           }

pattern TF :: String -> FilePath -> UnitTest
pattern TF testName verilogFile =
  UnitTest { annotFile = Nothing
           , testType  = Fail
           , ..
           }

data TestTree = SingleTest     UnitTest
              | TestCollection String [TestTree]

mkCollection :: String -> [UnitTest] -> TestTree
mkCollection name = TestCollection name . fmap SingleTest

abductionRoot, testDir, benchmarkDir, mipsDir :: FilePath
abductionRoot = "abduction"
testDir       = "test"
benchmarkDir  = "benchmarks"
mipsDir       = benchmarkDir </> "472-mips-pipelined"

allTests :: [TestTree]
allTests =
  [ simple
  , negative
  , mips
  , abduction
  , majorStubs
  , aesStubs
  , major
  ]

--------------------------------------------------------------------------------
simple :: TestTree
--------------------------------------------------------------------------------
simple = mkCollection "simple" $ ts ++ [t']
  where
    ts      = go <$> names
    t'      = T "stall-hand" $ "examples" </> "verilog" </> "stall.v"
    posDir  = testDir </> "verilog" </> "pos"
    go name = T name $ posDir </> name <.> "v"
    names   =
      [ "tr-test-1"
      , "tr-test-2"
      , "tr-test-3"
      , "tr-test-4"
      , "tr-test-5"
      , "tr-test-6"
      , "tr-test-9"
      , "tr-test-10"
      , "tr-test-11"
      , "merge-02"
      , "merge03"
      , "merge04-1"
      , "merge04"
      , "merge05"
      , "secverilog-01"
      , "nb-test-01"
      , "tr-submodule-01"
      , "submodule-02"
      , "submodule-03"
      , "submodule-04"
      , "tr-test-12"
      ]


--------------------------------------------------------------------------------
abduction :: TestTree
--------------------------------------------------------------------------------
abduction = mkCollection "abduction" ts
  where
    ts      = go <$> names
    go name = T name $ d </> name <.> "v"
    d       = testDir </> "abduction" </> "pos"
    names   = ["abduction-01"]


--------------------------------------------------------------------------------
mips :: TestTree
--------------------------------------------------------------------------------
mips = TestCollection "mips" [mipsModules, mipsNegatives, mipsStubs]

mipsModules :: TestTree
mipsModules = mkCollection "modules" $ go <$> names
  where
    go name = T name $ mipsDir </> name <.> "v"
    names = [ "reg32"
            , "mux3"
            , "control_pipeline"
            , "alu"
            , "alu_ctl"
            , "rom32"
            , "reg_file"
            , "mux3_test_01"
            , "mux3_test_02"
            , "mem32_test_01"
            ]

mipsNegatives :: TestTree
mipsNegatives = mkCollection "neg" $ (go <$> names) ++ mem32
  where
    go name = TF name $ mipsDir </> name <.> "v"
    names = [ "neg-mux3_test_02"
            ]
    mem32 = [ UnitTest { testName    = name
                       , verilogFile = mipsDir </> "mem32_test_01.v"
                       , annotFile   = Just $ mipsDir </> "annot-" <> name <.> "json"
                       , testType    = Fail
                       }
            | name <- [ "neg-mem32_test_01"
                      , "neg-mem32_test_02"
                      , "neg-mem32_test_03"
                      ]
            ]

mipsStubs :: TestTree
mipsStubs = mkCollection "stub" $ go <$> names
  where
    go (ver, name) = T ver $ mipsDir </> name <.> "v"
    names = [ ("v1", "472-mips-fragment")
            , ("v2", "472-mips-fragment-2")
            , ("v3", "472-mips-fragment-3")
            , ("v4", "472-mips-fragment-4")
            ]


--------------------------------------------------------------------------------
negative :: TestTree
--------------------------------------------------------------------------------
negative = mkCollection "negative" $ go <$> names
  where
    negDir = testDir </> "verilog" </> "neg"
    go name = TF name $ negDir </> name <.> "v"
    names = [ "neg-test-1"
            , "neg-test-2-v0"
            , "neg-test-2"
            , "neg-test-5"
            , "neg-test-6"
            , "tp"
            , "neg-test-11"
            , "secverilog-neg-01"
            , "secverilog-neg-02"
            , "neg-submodule-02"
            , "neg-submodule-03"
            , "neg-submodule-04"
            ]


--------------------------------------------------------------------------------
majorStubs :: TestTree
--------------------------------------------------------------------------------
majorStubs = mkCollection "major-stub" ts
  where
    b  = benchmarkDir
    shaDir = b </> "crypto_cores" </> "sha_core" </> "trunk" </> "rtl"
    aluDir = b </> "xcrypto-ref" </> "rtl" </> "coprocessor"
    ts = [ T "sha_stub_3" $ shaDir </> "sha256_stub_3.v"
         , T "mult_test"  $ aluDir </> "mult_test.v"
         ]


--------------------------------------------------------------------------------
aesStubs :: TestTree
--------------------------------------------------------------------------------
aesStubs = mkCollection "aes-stub" ts
  where
    d = benchmarkDir </> "crypto_cores" </> "tiny_aes" </> "trunk" </> "rtl"
    mkT name file = T name $ d </> file <.> "v"
    ts = [ mkT "table_lookup" "test1"
         , (mkT "one_round-0" "test2-0") { annotFile = Just $ IA.defaultAnnotFile $ d </> "test2.v" }
         , mkT "one_round" "test2"
         , (mkT "S4-0" "test3-0") { annotFile = Just $ IA.defaultAnnotFile $ d </> "test3.v" }
         , mkT "S4" "test3"
         , (mkT "final_round-0" "test4-0") { annotFile = Just $ IA.defaultAnnotFile $ d </> "test4.v" }
         , mkT "final_round" "test4"
         , (mkT "expand_key_type_A_256-0" "test5-0") { annotFile = Just $ IA.defaultAnnotFile $ d </> "test5.v" }
         , mkT "expand_key_type_A_256" "test5"
         , (mkT "expand_key_type_B_256-0" "test6-0") { annotFile = Just $ IA.defaultAnnotFile $ d </> "test6.v" }
         , mkT "expand_key_type_B_256" "test6"
         ]


--------------------------------------------------------------------------------
major :: TestTree
--------------------------------------------------------------------------------
major = mkCollection "major" ts
  where
    b  = benchmarkDir
    c  = b </> "crypto_cores"
    ts = [ T  "mips"        $ mipsDir </> "mips_pipeline.v"
         , T  "yarvi"       $ b </> "yarvi" </> "shared" </> "yarvi.v"
         , T  "sha"         $ c </> "sha_core" </> "trunk" </> "rtl" </> "sha256.v"
         , T  "fpu"         $ b </> "fpu" </> "verilog" </> "fpu.v"
         , TF "fpu-divider" $ b </> "fpu2" </> "divider" </> "divider.v"
         , TF "modexp"      $ c </> "RSA4096" </> "ModExp2" </> "ModExp.v"
         , T  "ctalu"       $ b </> "xcrypto-ref" </> "rtl" </> "coprocessor" </> "scarv_cop_palu.v"
         , T  "aes"         $ c </> "tiny_aes" </> "trunk" </> "rtl" </> "aes_256.v"
         ]
