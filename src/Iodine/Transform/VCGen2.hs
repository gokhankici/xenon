{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

-- {-# OPTIONS_GHC -Wno-missing-signatures #-}
-- {-# OPTIONS_GHC -Wno-redundant-constraints #-}
-- {-# OPTIONS_GHC -Wno-unused-binds #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-}
-- {-# OPTIONS_GHC -Wno-unused-matches #-}
-- {-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Iodine.Transform.VCGen2
  ( vcgen
  , VCGenOutput
  , getAllMIOutputs
  ) where

import           Iodine.Transform.VCGen (computeAllInitialEqualVars)
import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR hiding (isStar)
import           Iodine.Transform.Horn
import           Iodine.Transform.Normalize (NormalizeOutput2, TRSubs2, UpdateIndices(..))
import           Iodine.Transform.TransitionRelation
import           Iodine.Types
import           Iodine.Utils
import           Iodine.ConstantConfig

import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Effect.Error
import qualified Control.Effect.Trace as CET
import           Control.Effect.Writer
import           Control.Lens
import           Control.Monad
import           Data.Bifunctor
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntMap as IM
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Data.Traversable
import           Text.Printf

-- | State relevant to statements
data ThreadSt =
  ThreadSt { _currentSources       :: Ids
           , _currentSinks         :: Ids
           , _currentInitialEquals :: Ids
           , _currentAlwaysEquals  :: Ids
           , _currentAssertEquals  :: Ids
           }
  deriving (Show)

makeLenses ''ThreadSt

-- | global state
type G sig m = ( Has (Reader AnnotationFile) sig m
               , Has (Error IodineException) sig m
               , Has CET.Trace sig m
               , Has (Reader ModuleMap) sig m
               , Has (Reader SummaryMap) sig m
               , Has (Writer Output) sig m
               )

-- | vcgen state  = global effects + next var map
type FD sig m = ( G sig m
                , Has (Reader TRSubs2) sig m
                , Has (State HornVariableMap) sig m
                , Has (Reader InitialEqualVariables) sig m
                )

-- | module state = vcgen state + current module
type FDM sig m = ( FD sig m
                 , Has (Reader M) sig m
                 , Has (Reader HornVariables) sig m
                 , Has (Reader ThreadSt) sig m
                 , Has (Reader UpdateIndices) sig m
                 )

-- | stmt state = module state + current statement state
type FDS sig m = (FDM sig m, Has (Reader ThreadSt) sig m)

type A  = Int
type M  = Module A
type MI = ModuleInstance A
type AB = AlwaysBlock Int

type H                 = Horn ()
type Horns             = L H
type VCGenOutput       = (HornVariableMap, Horns)
type Substitutions     = HM.HashMap Id Int
type ModuleMap         = HM.HashMap Id M
type ModuleInstanceMap = HM.HashMap Id (L MI)
type ExprPair          = (HornExpr, HornExpr)

{- |
Verification condition generation creates the following 7 type of horn
constraints to encode our check:

1. Initialize: Encodes that initially, every tag is set to 0. We also encode
that the values of the variables that annotated as @initial_eq@ or @always_eq@
are the same. Keep in mind that @always_eq@ annotations apply to the rest of the
constraints listed below as well.

2. Tag Set: The tags of the sources are set to 1, and the tags of the rest of
the variables are set to zero.

3. Source Tag Reset: The tags of the sources are set to 0.

4. Next: Always blocks take a single step, and the variables values are updated.

5. Sink check: Checks that variables defined as sinks are tainted equally.

6. Assert equals check: Checks that variables that are annotated as @assert_eq@
always have the same value.

7. Non-interference checks: This is used to make sure that the invariants of
different always blocks are consistent under interference.
-}
vcgen :: G sig m => NormalizeOutput2 -> m VCGenOutput
vcgen (normalizedIR, trNextVariables2) = do
  ievs <- computeAllInitialEqualVars normalizedIR
  out@(_, horns) <- combine vcgenMod normalizedIR
    & runReader (InitialEqualVariables ievs)
    & runReader trNextVariables2
    & runReader (moduleInstancesMap normalizedIR)
    & runState  (HornVariableMap mempty)
  traceHorns horns
  return out

traceHorns :: G sig m => Horns -> m ()
traceHorns horns = do
  t "threads:"
  mm <- ask @ModuleMap
  for_ mm $ \m -> do
    t $ printf "* %d : %s" (getData m) (moduleName m)
    for_ (alwaysBlocks m) $ \ab ->
      t $ printf "    * %d : %s" (getData ab) (prettyShow $ abEvent ab)
    for_ (moduleInstances m) $ \mi ->
      t $ printf "    * %d : %s" (getData mi) (moduleInstanceName mi)
  t "horns:"
  for_ horns $ \h -> t $ printf "%3d: %s" (hornStmtId h) (show $ hornType h)
  t ""
  where t = CET.trace

vcgenMod :: FD sig m => Module Int -> m Horns
vcgenMod m@Module {..} = do
  assert (SQ.null gateStmts)
    "Gate statements should have been merged into always* blocks"
  assert singleBlockForEvent
    "There should be at most one always block for each event type"

  -- set module's horn variables
  mClks <- getClocks moduleName
  ModuleSummary{..} <- asks (HM.! moduleName)

  vs <- if includeEveryVariable
        then return $
             let allVars = foldl' (flip HS.insert) mempty $ variableName <$> variables
             in allVars `HS.difference` (mClks <> temporaryVariables)
        else do
          annots <- getModuleAnnotations moduleName
          let annotVars = annotationVariables (annots ^. moduleAnnotations)
              regs = let go acc (Register r) = HS.insert r acc
                         go acc (Wire _) = acc
                     in foldl' go mempty variables
              ps = HS.fromList (toList $ variableName . portVariable <$> ports) `HS.difference` mClks
              rbw = case alwaysBlocks of
                      Empty -> mempty
                      ab SQ.:<| Empty -> readBeforeWrittenTo ab mempty
                      _ -> error "unreachable"
          return $ annotVars <> ps <> regs <> rbw

  (threadSt, ui) <-
    case alwaysBlocks of
      Empty           -> return (emptyThreadSt, UpdateIndices mempty mempty)
      ab SQ.:<| Empty -> (,) <$> computeThreadStM m <*> asks (IM.! getData ab)
      _               -> error "unreachable"

  HornVariableMap hvm <- get
  put $ HornVariableMap $
    at (getThreadId m) ?~ vs $
    foldl' (\acc ab -> acc & at (getThreadId ab) ?~ vs) hvm alwaysBlocks

  moduleClauses
    & runReader m
    & runReader threadMap
    & runReader (HornVariables vs)
    & runReader threadSt
    & runReader ui

  where
    singleBlockForEvent = length alwaysBlocks <= 1
    allThreads = (AB <$> alwaysBlocks) <> (MI <$> moduleInstances)
    threadMap = foldl' (\tm t -> IM.insert (getData t) t tm) mempty allThreads

moduleClauses :: FDM sig m => m Horns
moduleClauses = do
  m@Module{..} <- ask
  simpleCheck <- isModuleSimple m
  CET.trace $ "moduleClauses simplecheck: " <> show simpleCheck
  if simpleCheck
    then return <$> combinatorialModuleInit
    else combine alwaysBlockClauses alwaysBlocks <||> summaryConstraint

alwaysBlockClauses :: FDM sig m => AlwaysBlock Int -> m Horns
alwaysBlockClauses ab = mconcat <$> sequence
  [ return        <$> initialize ab
  , maybeToMonoid <$> tagSet ab
  , maybeToMonoid <$> srcTagReset ab
  , return        <$> next ab
  , sinkCheck ab
  , assertEqCheck ab
  ]


-- -------------------------------------------------------------------------------------------------
initialize :: FDS sig m => AlwaysBlock Int -> m H
-- -------------------------------------------------------------------------------------------------
initialize ab = do
  currentModule <- ask @M
  UpdateIndices{..} <- ask
  let currentModuleName = moduleName currentModule
  srcs <- moduleInputs currentModule <$> getClocks currentModuleName
  let readOnlyVars = getReadOnlyVariables stmt <> srcs
      nbUpdates = HS.fromList (HM.keys lastNonBlockingIndex)
      readBeforeWrittenVars = readBeforeWrittenTo ab mempty `HS.difference` nbUpdates

  tagEqVars0 <- askHornVariables
  valEqVars0 <-
    HS.union <$>
    (HS.union <$> asks (^. currentInitialEquals) <*> asks (^. currentAlwaysEquals)) <*>
    asks ((HM.! moduleName currentModule) . getInitialEqualVariables)

  isTop <- isTopModule
  -- these are both the module inputs and variables that are written by other
  -- threads when generating an init clause for always blocks of submodules,
  -- these variables should stay as free variables
  let (zeroTagVars, valEqVars, extraSubs) =
        if   isTop
        then (tagEqVars0, valEqVars0, mempty)
        else
          let ct = tagEqVars0 `HS.difference` readOnlyVars
              ie = valEqVars0 `HS.difference` readOnlyVars
              es = foldMap
                   (\v -> sti2 <$> mkAllSubs v currentModuleName 0 1)
                   readOnlyVars
          in (ct, ie, es)

  let tagSubs = sti2 <$> foldl' (mkZeroTags currentModuleName) mempty zeroTagVars
      valSubs = sti2 <$> foldl' (valEquals currentModuleName) mempty valEqVars

  let unsanitizedStateVars = readBeforeWrittenVars `HS.difference` valEqVars
  unless (HS.null unsanitizedStateVars) $
    output [ "Variables read before written & not sanitized: "
             ++ show (currentModuleName, toList unsanitizedStateVars)
           ]

  trace "initialize" (currentModuleName, getThreadId ab, isTop)
  trace "initialize - zero" (toList zeroTagVars)
  trace "initialize - valeq" (toList valEqVars)
  trace "initialize - tagEqVars0" (toList tagEqVars0)

  -- for non-top module blocks, we do not assume that the sources are constant time
  -- however, we should keep their variables in the kvars
  return $
    Horn { hornHead   = makeKVar ab $ tagSubs <> valSubs <> extraSubs
         , hornBody   = HBool True
         , hornType   = Init
         , hornStmtId = getThreadId ab
         , hornData   = ()
         }
 where
   stmt = abStmt ab
   sti  = setThreadId ab
   sti2 = bimap sti sti
   mkZeroTags m subs v =
     subs |> (HVarTL0 v m, HBool False) |> (HVarTR0 v m, HBool False)
   valEquals m subs v =
     subs |> (HVarVL0 v m, HVarVR0 v m)

-- | create a list of expressions where the current module instances are
-- instantiated with the variables with their last blocking update index.
instantiateModules :: (FDS sig m, MakeKVar t) => t Int -> m (L HornExpr)
instantiateModules thread = do
  UpdateIndices{..} <- ask
  currentModule <- ask @M
  for (moduleInstances currentModule) $ \mi@ModuleInstance{..} -> do
    let currentModuleName = moduleName currentModule
    targetModule <- asks (hmGet 2 moduleInstanceType)
    let targetModuleName = moduleName targetModule
    targetModuleClocks <- getClocks moduleInstanceType
    let inputs  = moduleInputs targetModule targetModuleClocks
        outputs = moduleOutputs targetModule targetModuleClocks
        toVarIndex v = maybe 1 (+ 1) $ lastBlockingIndex ^. at v
        mkInputSubs i = do
          (t, f) <- (Value, val') |:> (Tag, tag')
          r <- LeftRun |:> RightRun
          let -- input port of the target module
              invParam = HVar0 i targetModuleName t r
              -- temporary variable created for the instance expression
              invArgVarName = "IodineTmpMIInput_" <> T.pack (show $ getData mi) <> "_" <> i
              invArgVar = sti $ HVar invArgVarName currentModuleName 1 t r 0
              -- expression used in the input port of the instance
              invArgExpr = sti $ f toVarIndex r $ hmGet 3 i moduleInstancePorts
          return ( mkEqual (invArgVar, invArgExpr)
                , (invParam, invArgVar)
                )
        mkOutputSubs o = do
          (t, r) <- allTagRuns
          let e = hmGet 4 o moduleInstancePorts
              rhs = if isVariable e
                    then sti $ HVar (varName e) currentModuleName 1 t r 0
                    else error $
                        "output port expresssion of a module instance should be a variable"
                        ++ show ModuleInstance{..}
          return (HVar0 o targetModuleName t r, rhs)
        inputSubs = foldMap mkInputSubs inputs
        subs = (snd <$> inputSubs) <> foldMap mkOutputSubs outputs
    return $ HAnd $ fmap fst inputSubs SQ.|> makeKVar targetModule subs
    where sti = setThreadId thread


combinatorialModuleInit :: FDM sig m => m H
combinatorialModuleInit = do
  m@Module{..} <- ask
  let sti = setThreadId m
  incrMiOutputs <- miOutputIncrementer m
  miExprs <- instantiateModules m
  (moduleSubs, abExprs) <- case alwaysBlocks of
    ab SQ.:<| Empty | abEvent ab == Star -> do
      abTR <- sti . updateVarIndex (+ 1) <$>
              transitionRelation (abStmt ab)
      abNext <- HM.map (+ 1) <$> getNextVars
      moduleAlwaysEqs <- moduleAlwaysEquals 1 abNext
      let moduleSubs = second sti <$> toSubs moduleName abNext
      return (moduleSubs, moduleAlwaysEqs |> abTR)
    Empty -> do
      let ps = variableName . portVariable <$> ports
          subs = mfold (\v -> second sti <$> mkAllSubs v moduleName 0 1) ps
      moduleAlwaysEqs <- moduleAlwaysEquals 1 mempty
      -- for_ miExprs $ \e -> trace "miexpr" e
      return (subs, moduleAlwaysEqs)
    _ -> error "unreachable"
  return $
    Horn { hornHead   = makeKVar m $ second incrMiOutputs <$> moduleSubs
         , hornBody   = HAnd $ incrMiOutputs <$> (abExprs <> miExprs)
         , hornType   = Init
         , hornStmtId = getThreadId m
         , hornData   = ()
         }

-- | the output ports of the instances do not show up in the next variable map.
-- this is used to increment the update index of these variables.
getAllMIOutputs :: (Has (Reader ModuleMap) sig m)
                 => M -> m Ids
getAllMIOutputs Module{..} =
  fmap fix $
  for (toList moduleInstances) $ \mi -> do
    targetModule :: M <- asks (HM.! moduleInstanceType mi)
    let ps = toList $ moduleOutputs targetModule mempty
        vs = varName . (moduleInstancePorts mi HM.!) <$> ps
    return vs
  where fix = HS.fromList . mconcat

miOutputIncrementer :: FDM sig m => M -> m (HornExpr -> HornExpr)
miOutputIncrementer m = do
  miOutputs <- getAllMIOutputs m
  return $
    updateVarIndex2 $
    \v n -> if v `elem` miOutputs then n + 1 else n

-- -------------------------------------------------------------------------------------------------
tagSet :: FDS sig m => AlwaysBlock Int -> m (Maybe H)
-- -------------------------------------------------------------------------------------------------
tagSet ab = withTopModule $ do
  (Module {..}, srcs, vars) <- tagSetHelper
  let nonSrcs             = HS.difference vars srcs
      addModuleName v     = (v, moduleName)
      tagsToSet           = addModuleName <$> toList srcs
      tagsToClear         = addModuleName <$> toList nonSrcs
      (eSet,   setSubs)   = updateTags 1 True  tagsToSet
      (eClear, clearSubs) = updateTags 1 False tagsToClear
      keepValues          = updateValues 1 moduleName vars
      body                = HAnd $ makeEmptyKVar ab <| eSet <> eClear <> keepValues
  let (body', subs) = (body, setSubs <> clearSubs)
  return $
    if HS.null srcs
    then Nothing
    else
      Just $
      Horn { hornHead   = makeKVar ab $ second sti <$> subs
           , hornBody   = sti body'
           , hornType   = TagSet
           , hornStmtId = getThreadId ab
           , hornData   = ()
           }
  where
    sti = setThreadId ab
{- HLINT ignore tagSet -}

tagSetHelper :: FDS sig m => m (Module Int, Ids, Ids)
tagSetHelper = do
  m <- ask @(Module Int)
  ms <- asks (HM.! moduleName m)
  vs <- askHornVariables
  srcs <- getCurrentSources
  return (m, srcs, vs `HS.difference` temporaryVariables ms)


-- -------------------------------------------------------------------------------------------------
srcTagReset :: FDS sig m => AlwaysBlock Int -> m (Maybe H)
-- -------------------------------------------------------------------------------------------------
srcTagReset ab = withTopModule $ do
  (Module {..}, srcs, vars) <- tagSetHelper
  let addModuleName v     = (v, moduleName)
      tagsToClear         = addModuleName <$> toList srcs
      (eClear, clearSubs) = updateTags 1 False tagsToClear
      keepValues          = updateValues 1 moduleName vars
      -- increment indices of srcs, clear the tags of the sources but keep the values
      body = HAnd $ makeEmptyKVar ab <| eClear <> keepValues -- inv holds on 0 indices
  let (body', subs) = (body, clearSubs)
  return $
    if HS.null srcs
    then Nothing
    else
      Just $
      Horn { hornHead   = makeKVar ab $ second sti <$> subs
           , hornBody   = sti body'
           , hornType   = SourceTagReset
           , hornStmtId = getThreadId ab
           , hornData   = ()
           }
  where sti = setThreadId ab

-- -------------------------------------------------------------------------------------------------
next :: FDS sig m => AlwaysBlock Int -> m H
-- -------------------------------------------------------------------------------------------------
next ab@AlwaysBlock{..} = do
  m@Module{..} <- ask @M
  initialSubs <-
    foldMap (\v -> second sti <$> mkAllSubs v moduleName 0 1)
    <$> askHornVariables
  let threadKVar = makeKVar ab initialSubs
  aes <- fmap (sti . uvi) <$> alwaysEqualEqualities
  tr <- sti . uvi <$> transitionRelation abStmt
  nextVars <- HM.map (+ 1) <$> getNextVars
  incrMiOutputs <- miOutputIncrementer m
  let subs  = second (incrMiOutputs . sti) <$> toSubs moduleName nextVars
  miExprs <- instantiateModules ab
  -- trace "miExprs nextStar" miExprs
  return $
    Horn { hornHead   = makeKVar ab subs
         , hornBody   = HAnd $ threadKVar <| aes <> (incrMiOutputs <$> miExprs |> tr)
         , hornType   = Next
         , hornStmtId = getThreadId ab
         , hornData   = ()
         }
  where
    sti = setThreadId ab
    uvi = updateVarIndex (+ 1)

-- -------------------------------------------------------------------------------------------------
sinkCheck :: FDS sig m => AB -> m Horns
-- -------------------------------------------------------------------------------------------------
sinkCheck ab = do
  Module {..} <- ask @M
  snks        <- asks (^. currentSinks)
  isTop <- isTopModule
  unless (HS.null snks || isTop) $
    throw "sink checks for non top module variables are not implemented yet"

  let threadKVar = makeEmptyKVar ab
  return $ foldl' (\hs v -> hs |> go threadKVar moduleName v) mempty snks
 where
  threadId = getThreadId ab
  go threadKVar m v =
    Horn { hornHead   = setThreadId ab $
                        HBinary HIff
                        (HVar v m 0 Tag LeftRun 0)
                        (HVar v m 0 Tag RightRun 0)
         , hornBody   = threadKVar
         , hornType   = TagEqual
         , hornStmtId = threadId
         , hornData   = ()
         }


-- -------------------------------------------------------------------------------------------------
assertEqCheck :: FDS sig m => AB -> m Horns
-- -------------------------------------------------------------------------------------------------
assertEqCheck ab = do
  Module {..} <- ask @M
  aes         <- asks (^. currentAssertEquals)
  isTop <- isTopModule
  unless (HS.null aes || isTop) $
    throw "assert checks for non top module variables are not implemented yet"
  let threadKVar = makeEmptyKVar ab
  return $ foldl' (\hs v -> hs |> go threadKVar moduleName v) mempty aes
 where
  threadId = getThreadId ab
  go threadKVar m v =
    Horn { hornHead   = setThreadId ab $
                        HBinary HEquals
                        (HVar v m 0 Value LeftRun 0)
                        (HVar v m 0 Value RightRun 0)
         , hornBody   = threadKVar
         , hornType   = AssertEqCheck
         , hornStmtId = threadId
         , hornData   = ()
         }


moduleAlwaysEquals :: FDM sig m => Int -> Substitutions -> m (L HornExpr)
moduleAlwaysEquals varIndex nxt = do
  currentModule <- ask
  let currentModuleName = moduleName currentModule
      sti = setThreadId currentModule
      mkAEs v =
        (sti <$> mkAEEquality v currentModuleName varIndex)
        <> (case HM.lookup v nxt of
               Just n  -> sti <$> mkAEEquality v currentModuleName n
               Nothing -> mempty
           )
  annots <- getAnnotations currentModuleName
  -- trace ("annots of " ++ show currentModuleName) annots
  return $ foldMap mkAEs (annots ^. alwaysEquals)


-- -----------------------------------------------------------------------------
summaryConstraint :: FDM sig m => m (L H)
-- -----------------------------------------------------------------------------
summaryConstraint = whenNotTop $ do
  m@Module{..} <- ask
  clks <- getClocks moduleName
  let portNames = variableName . portVariable <$> ports
      mkSubs v =
        if v `elem` clks
        then mempty
        else mkAllSubs v moduleName 0 1
      subs = second (setThreadId m) <$> foldMap mkSubs portNames
  case alwaysBlocks of
    Empty -> do
      miExprs <- instantiateModules m
      return $
        Horn { hornHead   = makeKVar m subs
             , hornBody   = HAnd miExprs
             , hornType   = Summary
             , hornStmtId = getThreadId m
             , hornData   = ()
             }
    ab SQ.:<| Empty -> do
      return $
        Horn { hornHead   = makeKVar m subs
             , hornBody   = makeKVar ab subs
             , hornType   = Summary
             , hornStmtId = getThreadId m
             , hornData   = ()
             }
    _ -> error "unreachable"
  where
    whenNotTop act = do
      istop <- isTopModule
      if istop then return mempty else return <$> act


-- -----------------------------------------------------------------------------
-- Helper functions
-- -----------------------------------------------------------------------------

newtype HornVariables = HornVariables { _getHornVariables :: Ids }

askHornVariables :: Has (Reader HornVariables) sig m => m Ids
askHornVariables = asks _getHornVariables

alwaysEqualEqualities :: FDS sig m => m (L HornExpr)
alwaysEqualEqualities = do
  Module {..} <- ask @M
  nextVars <- getNextVars
  let addEquals exprs v = exprs <> mkAEEquality v moduleName 0
  let go exprs v =
        let exprs' = addEquals exprs v
        in case HM.lookup v nextVars of
          Just n  -> exprs' <> mkAEEquality v moduleName n
          Nothing -> exprs'
  foldl' go mempty <$> asks (^. currentAlwaysEquals)

mkAEEquality :: Id -> Id -> Int -> L HornExpr
mkAEEquality v m n = mkEqual <$> pairs
  where
    pairs = do
      t <- Value |:> Tag
      return (HVar v m n t LeftRun 0, HVar v m n t RightRun 0)

-- | get the last index of each variable after transitioning from variables with
-- index 0
getNextVars :: FDM sig m => m Substitutions
getNextVars = do
  UpdateIndices{..} <- ask
  hornVars <- askHornVariables
  let nextVarMap = lastBlockingIndex <> lastNonBlockingIndex
  return $
    foldl'
    (\m v -> HM.insertWith (\_newIndex oldIndex -> oldIndex) v 0 m)
    nextVarMap hornVars

toSubs :: Id                    -- ^ module name
       -> Substitutions         -- ^ substitution map
       -> L ExprPair            -- ^ variable updates for the kvar
toSubs m = HM.foldlWithKey' go mempty
 where go subs v n = subs <> mkAllSubs v m 0 n


-- | variable name -> module name -> lhs index -> rhs index -> horn variable
-- pairs for the equalities of vl, vr, tl, tr
mkAllSubs, mkTagSubs, mkValueSubs :: Id -> Id -> Int -> Int -> L ExprPair
mkAllSubs   v m n1 n2 = mkTagSubs v m n1 n2 <> mkValueSubs v m n1 n2
mkTagSubs   v m n1 n2 = (\r -> (HVar v m n1 Tag r 0,   HVar v m n2 Tag r 0))   <$> (LeftRun |:> RightRun)
mkValueSubs v m n1 n2 = (\r -> (HVar v m n1 Value r 0, HVar v m n2 Value r 0)) <$> (LeftRun |:> RightRun)


-- | creates a map between submodule names and all the instances of it
moduleInstancesMap :: L M -> ModuleInstanceMap
moduleInstancesMap = foldl' handleModule mempty
  where
    handleModule miMap Module{..} =
      foldl' handleInstance miMap moduleInstances
    handleInstance miMap mi@ModuleInstance{..} =
      let mis' = case HM.lookup moduleInstanceType miMap of
                   Nothing  -> SQ.singleton mi
                   Just mis -> mis SQ.|> mi
      in HM.insert moduleInstanceType mis' miMap


isTopModule :: (Has (Reader (Module Int)) sig m, Has (Reader AnnotationFile) sig m) => m Bool
isTopModule = ask @M >>= isTopModule'

isTopModule' :: Has (Reader AnnotationFile) sig m => Module a -> m Bool
isTopModule' Module{..} = do
  topModuleName <- asks @AnnotationFile (^. afTopModule)
  return $ moduleName == topModuleName


withTopModule :: FDM sig m => m (Maybe a) -> m (Maybe a)
withTopModule act = do
  top <- isTopModule
  if top then act else return Nothing

getCurrentSources :: FDS sig m => m Ids
getCurrentSources = do
  top <- isTopModule
  if top
    then asks (^. currentSources)
    else do vars <- askHornVariables
            inputs <- moduleInputs <$> ask @M <*> getCurrentClocks
            return $ HS.filter (`elem` inputs) vars

-- >>> updateTags 3 True $ bimap T.pack T.pack <$> [("Mod1", "Var1"), ("Mod2", "Var2")]
{- (fromList [TL.Var1.T0.Mod1.3 <=> True,
              TR.Var1.T0.Mod1.3 <=> True,
              TL.Var2.T0.Mod2.3 <=> True,
              TR.Var2.T0.Mod2.3 <=> True],
    fromList [(TL.Var1.T0.Mod1.0,TL.Var1.T0.Mod1.3),
              (TR.Var1.T0.Mod1.0,TR.Var1.T0.Mod1.3),
              (TL.Var2.T0.Mod2.0,TL.Var2.T0.Mod2.3),
              (TR.Var2.T0.Mod2.0,TR.Var2.T0.Mod2.3)])
-}
updateTags :: Foldable t
           => Int
           -> Bool
           -> t (Id, Id)
           -> (L HornExpr, L ExprPair)
updateTags n b =
  foldl'
  (\(es, ss) (v, m) ->
     let es' = es
               -- <> (mkEqual <$> mkValueSubs v m n 0)
               |> mkEqual (HVarTL v m n, HBool b)
               |> mkEqual (HVarTR v m n, HBool b)
         ss' = ss <> mkTagSubs v m 0 n
     in (es', ss'))
  (mempty, mempty)

updateValues :: Foldable t => Int -> Id -> t Id -> L HornExpr
updateValues n moduleName =
  foldl' (\acc v -> acc <> (mkEqual <$> mkValueSubs v moduleName n 0)) mempty


throw :: G sig m => String -> m a
throw = throwError . IE VCGen

getCurrentClocks :: FDM sig m => m Ids
getCurrentClocks = asks @M moduleName >>= getClocks

computeThreadStM :: G sig m => M -> m ThreadSt
computeThreadStM Module{..} = do
  as <- getAnnotations moduleName
  return $
    ThreadSt
    { _currentSources       = as ^. sources
    , _currentSinks         = as ^. sinks
    , _currentInitialEquals = as ^. initialEquals
    , _currentAlwaysEquals  = as ^. alwaysEquals
    , _currentAssertEquals  = as ^. assertEquals
    }

emptyThreadSt :: ThreadSt
emptyThreadSt =
  ThreadSt { _currentSources       = mempty
           , _currentSinks         = mempty
           , _currentInitialEquals = mempty
           , _currentAlwaysEquals  = mempty
           , _currentAssertEquals  = mempty
           }
newtype InitialEqualVariables = InitialEqualVariables { getInitialEqualVariables :: HM.HashMap Id Ids }