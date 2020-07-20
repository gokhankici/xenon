{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Iodine.Transform.VCGen
  ( vcgen
  , VCGenOutput
  , HornVariableMap
  , askHornVariables
  , isModuleSimple
  , computeAllInitialEqualVars
  )
where

import           Iodine.Analyze.DependencyGraph (VarDepEdgeType)
import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Horn
import           Iodine.Transform.Normalize (NormalizeOutput)
import           Iodine.Transform.TransitionRelation
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Effect.Error
import           Control.Effect.Trace (Trace)
import           Control.Effect.Writer
import           Control.Lens
import           Control.Monad
import           Data.Bifunctor
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import           Data.List
import           Data.Maybe
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Data.Traversable

-- | State relevant to statements
data ThreadSt =
  ThreadSt { _currentVariables        :: Ids -- ^ all vars in this block
           , _currentWrittenVariables :: Ids
           -- the rest is the filtered version of the Annotations type
           , _currentSources          :: Ids
           , _currentSinks            :: Ids
           , _currentInitialEquals    :: Ids
           , _currentAlwaysEquals     :: Ids
           , _currentAssertEquals     :: Ids

           }
  deriving (Show)

makeLenses ''ThreadSt

-- | global state
type G sig m = ( Has (Reader AnnotationFile) sig m
               , Has (Error IodineException) sig m
               , Has Trace sig m
               , Has (Reader ModuleMap) sig m
               , Has (Reader SummaryMap) sig m
               , Has (Writer Output) sig m
               -- , Effect sig
               )

type G' sig m = (G sig m, Has (Reader InitialEqualVariables) sig m)

-- | vcgen state  = global effects + next var map
type FD sig m = (G' sig m, Has (Reader NextVars) sig m, Has (State  HornVariableMap) sig m)

-- | module state = vcgen state + current module
type FDM sig m = ( FD sig m
                 , Has (Reader (Module Int)) sig m
                 , Has (Reader (IM.IntMap TI)) sig m
                 , Has (Reader (IM.IntMap ThreadSt)) sig m
                 )

-- | stmt state = module state + current statement state
type FDS sig m = (FDM sig m, Has (Reader ThreadSt) sig m)

type A = Int
type M = Module A

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
vcgen :: G sig m => NormalizeOutput -> m VCGenOutput
vcgen (normalizedIR, trNextVariables) = do
  ievs <- computeAllInitialEqualVars normalizedIR
  combine vcgenMod normalizedIR
    & runReader (InitialEqualVariables ievs)
    & runReader (NextVars trNextVariables)
    & runReader (moduleInstancesMap normalizedIR)
    & runState  (HornVariableMap mempty)


vcgenMod :: FD sig m => Module Int -> m Horns
vcgenMod m@Module {..} = do
  assert (SQ.null gateStmts)
    "Gate statements should have been merged into always* blocks"
  assert singleBlockForEvent
    "There should be at most one always block for each event type"

  -- set module's horn variables
  mClks <- getClocks moduleName
  setHornVariables m $ getVariables m `HS.difference` mClks

  -- set each thread's horn variables
  isTop <- isTopModule' m
  for_ alwaysBlocks $ \ab -> do
    let abVars = getVariables ab
        hVars = if isTop || isStar ab
                then abVars
                else abVars <> moduleInputs m mClks
    setHornVariables ab hVars

  runReader m $ runReader threadMap $ do
    threadStMap :: IM.IntMap ThreadSt <-
      execState IM.empty $
      for allThreads $ \thread -> do
      threadSt  <- computeThreadStM m thread
      modify (IM.insert (getData thread) threadSt)
    moduleClauses & runReader threadStMap
  where
    allThreads          = (AB <$> alwaysBlocks) <> (MI <$> moduleInstances)
    allEvents           = void <$> toList (abEvent <$> alwaysBlocks)
    singleBlockForEvent = length allEvents == length (nub allEvents)
    threadMap           = foldl' (\tm t -> IM.insert (getData t) t tm) mempty allThreads

moduleClauses :: FDM sig m => m Horns
moduleClauses = do
  m@Module{..} <- ask
  simpleCheck <- isModuleSimple m
  if simpleCheck
    then SQ.singleton <$> combinatorialModuleInit
    else do
    let allThreads = (AB <$> alwaysBlocks) <> (MI <$> moduleInstances)
    combine alwaysBlockClauses alwaysBlocks
      <||> combine (\mi -> let t = MI mi
                           in withAB t $
                              sinkCheck t <||> assertEqCheck t
                   ) moduleInstances
      <||> interferenceChecks allThreads
      <||> (SQ.singleton <$> summaryConstraint)
      -- <||> debuggingConstraints

isModuleSimple :: ( Has (Reader AnnotationFile) sig m
                  , Has (Reader SummaryMap) sig m
                  )
               => Module Int
               -> m Bool
isModuleSimple m =
  (&&) <$> (not <$> isTopModule' m) <*> asks (isCombinatorial . hmGet 8 (moduleName m))

alwaysBlockClauses :: FDM sig m => AlwaysBlock Int -> m Horns
alwaysBlockClauses ab =
  withAB t
  $ (SQ.singleton <$> initialize ab)
  <||> (maybeToMonoid <$> tagSet ab)
  <||> (maybeToMonoid <$> srcTagReset ab)
   ||> next ab
  <||> sinkCheck t
  <||> assertEqCheck t
  where t = AB ab


-- -------------------------------------------------------------------------------------------------
initialize :: FDS sig m => AlwaysBlock Int -> m H
-- -------------------------------------------------------------------------------------------------
initialize ab = do
  currentModule <- ask @M
  let currentModuleName = moduleName currentModule

  tagEqVars0 <- getHornVariables ab
  valEqVars0 <- HS.union <$> asks (^. currentInitialEquals) <*> asks (^. currentAlwaysEquals)

  isTop <- isTopModule
  -- these are both the module inputs and variables that are written by other
  -- threads when generating an init clause for always blocks of submodules,
  -- these variables should stay as free variables
  srcs <- moduleInputs currentModule <$> getClocks currentModuleName
  let readOnlyVars = getReadOnlyVariables stmt <> srcs
      readBeforeWrittenVars = readBeforeWrittenTo ab mempty
  let (zeroTagVars, valEqVars, extraSubs) =
        if   isTop
        then (tagEqVars0, valEqVars0, mempty)
        else
          let ct = if   isStar ab
                   then readBeforeWrittenVars
                   else tagEqVars0 `HS.difference` readOnlyVars
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

  trace "initialize" (currentModuleName, getThreadId ab, isTop, isStar ab)
  trace "initialize - zero" (toList zeroTagVars)
  trace "initialize - valeq" (toList valEqVars)

  -- hornVars <- getHornVariables ab
  -- trace "non initial_eq vals" (getData ab, toList $ hornVars `HS.difference` valEqVars)

  (cond, subs) <-
    if isStar ab
    then do nxt <- HM.map (+1) <$> getNextVars ab
            let tr = sti $ uvi $ transitionRelation (abStmt ab)
                cond1 = uvi . mkEqual <$> tagSubs
                cond2 = uvi . mkEqual <$> valSubs
                cond3 =
                  foldl'
                  (\es v ->
                     case HM.lookup v nxt of
                       Nothing -> es
                       Just n  ->
                         es
                         |> mkEqual ( sti $ HVarVL v currentModuleName n
                                    , sti $ HVarVR v currentModuleName n)
                  ) mempty valEqVars
                nxt' = if isTop
                       then nxt
                       else HM.filterWithKey (\v _ -> v `notElem` readOnlyVars) nxt
                subs = sti2 <$> toSubs currentModuleName nxt'
            return (HAnd (cond1 <> cond2 <> cond3 |> tr), subs)
    else return (HBool True, tagSubs <> valSubs)

  -- for non-top module blocks, we do not assume that the sources are constant time
  -- however, we should keep their variables in the kvars
  let subs' = subs <> extraSubs

  return $
    Horn { hornHead   = makeKVar ab subs'
         , hornBody   = cond
         , hornType   = Init
         , hornStmtId = getThreadId ab
         , hornData   = ()
         }
 where
   stmt = abStmt ab
   sti = setThreadId ab
   sti2 = bimap sti sti
   uvi = updateVarIndex (+ 1)
   mkZeroTags m subs v =
     subs |> (HVarTL0 v m, HBool False) |> (HVarTR0 v m, HBool False)
   valEquals m subs v =
     subs |> (HVarVL0 v m, HVarVR0 v m)


combinatorialModuleInit :: FDM sig m => m H
combinatorialModuleInit = do
  m@Module{..} <- ask
  let sti = setThreadId m
      ab = case alwaysBlocks of
             a SQ.:<| Empty | abEvent a == Star -> a
             _ -> error "unreachable"
      abTR = sti $ updateVarIndex (+ 1) $
             transitionRelation (abStmt ab)
  miExprs <- for moduleInstances instantiateMI
  abNext <- HM.map (+ 1) <$> getNextVars ab
  moduleAlwaysEqs <- moduleAlwaysEquals 1 abNext
  let moduleSubs = second sti <$> toSubs moduleName abNext
  return $
    Horn { hornHead   = makeKVar m moduleSubs
         , hornBody   = HAnd $ moduleAlwaysEqs <> miExprs |> abTR
         , hornType   = Init
         , hornStmtId = getThreadId m
         , hornData   = ()
         }


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
  (body', subs) <-
    if isStar ab
    then do
      aes      <- fmap (updateVarIndex (+ 1)) <$> alwaysEqualEqualities thread
      nextVars <- HM.map (+ 1) <$> getNextVars ab
      let tr = updateVarIndex (+ 1) $ transitionRelation (abStmt ab)
      -- inv holds on 0 indices
      -- increment all indices, keep values but update tags
      -- always_eq on 1 indices and last hold
      -- transition starting from 1 indices
      return ( HAnd ((body <| aes) |> tr)
             , toSubsTags moduleName nextVars
             )
    else return (body, setSubs <> clearSubs)
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
    thread = AB ab
    sti = setThreadId ab
{- HLINT ignore tagSet -}

tagSetHelper :: FDS sig m => m (Module Int, Ids, Ids)
tagSetHelper = (,,) <$> ask @(Module Int) <*> getCurrentSources <*> asks (^. currentVariables)


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
  (body', subs) <-
    if isStar ab
    then do
      let nonSrcs = HS.difference vars srcs
          nonSrcUpdates = keepEverything 1 $ addModuleName <$> toList nonSrcs
      aes       <- fmap (updateVarIndex (+ 1)) <$> alwaysEqualEqualities thread
      nextVars  <- HM.map (+ 1) <$> getNextVars ab
      let tr    = updateVarIndex (+ 1) $ transitionRelation (abStmt ab)
      -- increment indices of non srcs, keep everything
      -- always_eq on 1 indices and last hold
      -- transition starting from 1 indices
      return ( HAnd $ body <| nonSrcUpdates <> (aes |> tr)
             , toSubsTags moduleName nextVars
             )
    else return (body, clearSubs)
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
  where
    thread = AB ab
    sti = setThreadId ab
    keepEverything n =
      foldl' (\es (v, m) -> es <> (mkEqual <$> mkAllSubs v m n 0)) mempty

-- -------------------------------------------------------------------------------------------------
next, nextStar, nextTopClk, nextSubClock :: FDS sig m => AlwaysBlock Int -> m H
-- -------------------------------------------------------------------------------------------------
next ab = do
  isTop <- isTopModule
  if | isStar ab -> nextStar ab
     | isTop     -> nextTopClk ab
     | otherwise -> nextSubClock ab

nextStar ab@AlwaysBlock{..} = do
  Module {..} <- ask @M
  initialSubs <-
    foldMap (\v -> second sti <$> mkAllSubs v moduleName 0 1)
    <$> getHornVariables ab
  let threadKVar = makeKVar ab initialSubs
  aes <- fmap (sti . uvi) <$> alwaysEqualEqualities (AB ab)
  let tr = sti $ uvi $ transitionRelation abStmt
  nextVars <- HM.map (+ 1) <$> getNextVars ab
  let subs  = second sti <$> toSubs moduleName nextVars
  return $
    Horn { hornHead   = makeKVar ab subs
         , hornBody   = HAnd $ (threadKVar <| aes) |> tr
         , hornType   = Next
         , hornStmtId = getThreadId ab
         , hornData   = ()
         }
  where
    sti = setThreadId ab
    uvi = updateVarIndex (+ 1)

nextTopClk ab@AlwaysBlock{..} = do
  Module {..} <- ask @M
  case find ((/= thisTid) . getThreadId) alwaysBlocks of
    Nothing     -> nextStar ab
    Just starAB -> do
      h <- nextStar ab
      overlappingVars <-
        fmap toSequence
        $ HS.intersection
        <$> asks (view currentVariables . (IM.! thisTid))
        <*> asks (view currentVariables . (IM.! getThreadId starAB))
      let starKVar = makeKVar starAB (overlappingVars >>= mkSub)
      return $ h { hornBody = HAnd $ starKVar |:> hornBody h }
  where
    thisTid = getThreadId ab
    mkSub v = second (setThreadId ab) <$> mkAllSubs v v 0 1

nextSubClock ab@AlwaysBlock{..} = do
  m@Module{..} <- ask
  ms :: ModuleSummary <- asks (hmGet 9 moduleName)
  depThreadIds <- IS.delete (getData ab) <$> getAllDependencies (AB ab) & runReader ms
  -- srcs <- moduleInputs m <$> getClocks moduleName
  -- hornVars <- getHornVariables ab
  -- let abReadOnlyVars = getReadOnlyVariables abStmt
  --     extraSrcs     = srcs `HS.difference` abReadOnlyVars
      -- readOnlyVars  = abReadOnlyVars <> extraSrcs
  --     writtenVars   = hornVars `HS.difference` readOnlyVars
  -- trace "nextSubClock" (getThreadId ab, toList writtenVars)
  depThreadInstances <-
    for (IS.foldl' (|>) SQ.empty depThreadIds) $ \depThreadId -> do
    depThread <- asks (IM.! depThreadId)
    case depThread of
      AB depAB -> instantiateAB depAB mempty
      MI depMI -> instantiateMI depMI
  let sti  = setThreadId m
      uvi1 = updateVarIndex (+ 1)
      tr   = uvi1 $ sti $ transitionRelation abStmt
  abNext <- HM.map (+ 1) <$> getNextVars ab
  (body, hd) <- interferenceReaderExpr ab mempty abNext
  let subs = case hd of
               KVar _ s -> s
               _ -> error "unreachable"
  -- let extraSrcSubs =
  --       foldMap (\v -> second sti <$> mkAllSubs v moduleName 0 1) extraSrcs
  return $
    -- Horn { hornHead   = makeKVar ab $ extraSrcSubs <> subs
    Horn { hornHead   = makeKVar ab subs
         , hornBody   = HAnd $ depThreadInstances <> body |> tr
         , hornType   = Next
         , hornStmtId = getThreadId ab
         , hornData   = ()
         }

-- -------------------------------------------------------------------------------------------------
sinkCheck :: FDS sig m => TI -> m Horns
-- -------------------------------------------------------------------------------------------------
sinkCheck thread@(MI _) = do
  snks <- asks (^. currentSinks)
  writtenVars <- getUpdatedVariables thread
  when (snks `intersects` writtenVars) $
    throw "not implemented sink check of module instance outputs yet"
  return mempty

sinkCheck (AB ab) = do
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
assertEqCheck :: FDS sig m => TI -> m Horns
-- -------------------------------------------------------------------------------------------------
assertEqCheck thread@(MI _) = do
  snks <- asks (^. currentAssertEquals)
  writtenVars <- getUpdatedVariables thread
  when (snks `intersects` writtenVars) $
    throw "not implemented value assert check of module instance outputs yet"
  return mempty

assertEqCheck (AB ab) = do
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


-- -------------------------------------------------------------------------------------------------
interferenceChecks :: FDM sig m => L TI -> m Horns
-- -------------------------------------------------------------------------------------------------
interferenceChecks abmis = do
  isTop <- isTopModule
  if isTop
    then traverse_ interferenceCheck abmis
         & execState @Horns mempty
    else return mempty

interferenceCheck :: (FDM sig m, Has (State Horns) sig m)
                  => TI -> m ()
interferenceCheck (MI _)  = return ()
interferenceCheck (AB readAB) = do
  Module{..} <- ask @M
  ModuleSummary{..} <- asks (hmGet 1 moduleName)
  -- trace "threadDependencies" threadDependencies
  let readTid = getThreadId readAB
      threadDeps = filter (/= readTid) $ G.pre threadDependencies readTid
  for_ threadDeps $ \writeTid -> do
    writeThread <- asks (IM.! writeTid)
    overlappingVars <-
      HS.intersection
      <$> asks (view currentWrittenVariables . (IM.! writeTid))
      <*> asks (view currentVariables . (IM.! readTid))
    when (HS.null overlappingVars) $ do
      trace "overlapping variables" (toList overlappingVars)
      throw "overlapping variables should not be empty here"
    case writeThread of
      AB writeAB ->
        interferenceCheckAB writeAB readAB overlappingVars >>= addHorn
      MI writeMI ->
        interferenceCheckMI writeMI readAB overlappingVars >>= addHorn

addHorn :: Has (State Horns) sig m => H -> m ()
addHorn h = modify (SQ.|> h)

interferenceCheckMI :: FDM sig m
                    => ModuleInstance Int -- ^ instance that does the update (writer)
                    -> AlwaysBlock Int    -- ^ always block being updated (reader)
                    -> Ids                -- ^ the variables being updated
                    -> m H
interferenceCheckMI writeMI readAB overlappingVars = do
  m@Module{..} <- ask
  moduleSummary :: ModuleSummary <- asks (hmGet 9 moduleName)
  depThreadIds <-
    IS.delete (getData readAB)
    <$> getAllDependencies (MI writeMI) & runReader moduleSummary
  -- trace "interferenceCheckMI" (IS.toList depThreadIds, getData writeMI, getData readAB, toList overlappingVars)
  depThreadInstances <-
    for (toSeq depThreadIds) $ \depThreadId -> do
    depThread <- asks (IM.! depThreadId)
    case depThread of
      AB depAB -> instantiateAB depAB overlappingVars
      MI depMI -> instantiateMI depMI
  writeInstance <- instantiateMI writeMI
  let writeNext = foldl' (\nxt v -> HM.insert v 1 nxt) mempty overlappingVars
  (readBodyExpr, readHornHead) <-
    interferenceReaderExpr readAB overlappingVars writeNext
  -- if we're in the top module, we need constant time assumptions for the
  -- source variables
  isTop <- isTopModule
  topModuleExprs <-
    if isTop
    then do let mkTagEq v =
                  setThreadId m $
                  mkEqual
                  ( HVarTL v moduleName 1
                  , HVarTR v moduleName 1
                  )
            foldl' (\acc v -> acc |> mkTagEq v)  mempty
              <$> getSources moduleName
    else return mempty
  alwaysEqualVariables <-
    view alwaysEquals
    <$> getAnnotations moduleName
  let aeExprs =
        foldl'
        (\acc v ->
           let e = setThreadId m $ mkEqual
                   ( HVarVL v moduleName 1
                   , HVarVR v moduleName 1
                   )
           in acc SQ.|> e
        ) mempty alwaysEqualVariables
  let otherThreadIds = getData writeMI : IS.toList depThreadIds
  return $
    Horn { hornHead   = readHornHead
         , hornBody   = HAnd $
                        topModuleExprs <> aeExprs <>
                        (depThreadInstances |> writeInstance)
                        <> readBodyExpr
         , hornType   = Interference otherThreadIds
         , hornStmtId = getThreadId readAB
         , hornData   = ()
         }
  where
    toSeq = IS.foldl' (|>) SQ.empty


-- | return the interference check
interferenceCheckAB :: FDM sig m
                    => AlwaysBlock Int -- ^ always block that does the update (writer)
                    -> AlwaysBlock Int -- ^ always block being updated (reader)
                    -> Ids             -- ^ the variables being updated
                    -> m H
interferenceCheckAB writeAB readAB overlappingVars= do
  -- trace "interferenceCheckAB" (getData writeAB, getData readAB, toList overlappingVars)
  currentModule <- ask @(Module Int)
  writeInstance <- instantiateAB writeAB mempty
  let sti     = setThreadId currentModule
      uvi1    = updateVarIndex (+ 1)
      writeTR = uvi1 $ sti $ transitionRelation (abStmt writeAB)
  aes <-
    let t = AB writeAB
    in withAB t $
       fmap (setThreadId currentModule . updateVarIndex (+ 1)) <$>
       alwaysEqualEqualities t
  writeNext <- HM.map (+ 1) <$> getNextVars writeAB
  (body, hd) <- interferenceReaderExpr readAB overlappingVars writeNext
  return $
    Horn { hornHead   = hd
         , hornBody   = HAnd $ writeInstance <| (aes |> writeTR) <> body
         , hornType   = Interference [getData writeAB]
         , hornStmtId = getThreadId readAB
         , hornData   = ()
         }

interferenceReaderExpr :: FDM sig m
                       => AlwaysBlock Int              -- ^ always block being updated (reader)
                       -> Ids                          -- ^ the variables being updated
                       -> Substitutions                -- ^ substitution map of the write thread
                       -> m (L HornExpr, HornExpr) -- ^ body & head expression
interferenceReaderExpr readAB overlappingVars writeNext = do
  currentModule <- ask @(Module Int)
  let currentModuleName = moduleName currentModule
      sti = setThreadId currentModule
  readNext <- getNextVars readAB
  (body, subNext) <-
    if isStar readAB
    then do
      readHornVars <- getHornVariables readAB
      let maxWriteN = maximum writeNext
          uviN = updateVarIndex (+ maxWriteN)
          pullVarsToN =
            foldMap
            (\rv ->
               let extraSubs n =
                     sti . mkEqual <$> mkAllSubs rv currentModuleName maxWriteN n
               in case HM.lookup rv writeNext of
                    Just n | n == maxWriteN -> mempty
                           | n <  maxWriteN -> extraSubs n
                           | otherwise      -> error "unreachable"
                    Nothing | maxWriteN > 1 -> extraSubs 1
                            | otherwise     -> mempty
            )
            readHornVars
      let readTR = uviN $ sti $ transitionRelation (abStmt readAB)
      return ( pullVarsToN |> readTR
             , HM.map (+ maxWriteN) readNext
             )
    else
      return ( mempty
             , HM.mapWithKey (\v _ -> fromMaybe 1 $ HM.lookup v writeNext) readNext
             )

  readInstance <- instantiateAB readAB overlappingVars
  moduleAlwaysEqs <- moduleAlwaysEquals 1 subNext
  let subs =  second sti <$> toSubs currentModuleName subNext

  return ( readInstance <| moduleAlwaysEqs <> body
         , makeKVar readAB subs
         )

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


-- | Instantiate the always block with variable index = 1 and thread index equal
-- to the current module's id. The given set of variables are excluded from the
-- instantiation.
instantiateAB :: FDM sig m => AlwaysBlock Int -> Ids -> m HornExpr
instantiateAB ab excludedVars = do
  m@Module{..} <- ask
  let sti = setThreadId m
      mkEqs = fmap (mkEqual . bimap (setThreadId ab) sti) . foldMap (\v -> mkAllSubs v moduleName 0 1)
  instanceVars <- mkEqs . (`HS.difference` excludedVars) <$> getHornVariables ab
  return $ HAnd $ makeKVar ab mempty <| instanceVars


-- | instantiate the given module instance with variable index = 1 and thread
-- index equal to the current module's
instantiateMI :: FDM sig m => ModuleInstance Int -> m HornExpr
instantiateMI mi = instantiateMI' mi 1

instantiateMI' :: FDM sig m => ModuleInstance Int -> Int -> m HornExpr
instantiateMI' mi@ModuleInstance{..} varIndex = do
  currentModule <- ask
  let currentModuleName = moduleName currentModule
  targetModule <- asks (hmGet 2 moduleInstanceType)
  let targetModuleName = moduleName targetModule
  targetModuleClocks <- getClocks moduleInstanceType
  let inputs  = moduleInputs targetModule targetModuleClocks
      outputs = moduleOutputs targetModule targetModuleClocks
      sti     = setThreadId currentModule
      mkInputSubs i = do
        (t, f) <- (Value, val) |:> (Tag, tag)
        r <- LeftRun |:> RightRun
        let invParam = HVar0 i targetModuleName t r
            invArgVarName = "IodineTmpMIInput_" <> T.pack (show $ getData mi) <> "_" <> i
            invArgVar = sti $ HVar0 invArgVarName currentModuleName t r
            invArgExpr = sti $ updateVarIndex (const varIndex) $
                         f r $ hmGet 3 i moduleInstancePorts
        return ( mkEqual (invArgVar, invArgExpr)
               , (invParam, invArgVar)
               )
      mkOutputSubs o = do
        (t, r) <- allTagRuns
        let e = hmGet 4 o moduleInstancePorts
            rhs = if isVariable e
                  then HVar (varName e) currentModuleName varIndex t r 0
                  else error $
                       "output port expresssion of a module instance should be a variable"
                       ++ show ModuleInstance{..}
        return ( HVar0 o targetModuleName t r
               , rhs
               )
      inputSubs = foldMap mkInputSubs inputs
      subs = second (setThreadId currentModule)
             <$> (fmap snd inputSubs <> foldMap mkOutputSubs outputs)
  return $ HAnd $ fmap fst inputSubs SQ.|> makeKVar targetModule subs

-- -----------------------------------------------------------------------------
summaryConstraint :: FDM sig m => m H
-- -----------------------------------------------------------------------------
summaryConstraint = do
  m@Module{..} <- ask
  clks <- getClocks moduleName
  let portNames = variableName . portVariable <$> ports
      mkSubs v =
        if v `elem` clks
        then mempty
        else mkAllSubs v moduleName 0 1
      subs = second (setThreadId m) <$> foldMap mkSubs portNames
  body <- instantiateAllThreads
  return $
    Horn { hornHead   = makeKVar m subs
         , hornBody   = body
         , hornType   = Summary
         , hornStmtId = getThreadId m
         , hornData   = ()
         }

instantiateAllThreads :: FDM sig m => m HornExpr
instantiateAllThreads = do
  currentModule <- ask
  instances <-
    mappend
    <$> for (alwaysBlocks currentModule) (`instantiateAB` mempty)
    <*> traverse instantiateMI (moduleInstances currentModule)
  return $ HAnd instances


-- -----------------------------------------------------------------------------
-- Helper functions
-- -----------------------------------------------------------------------------

type TI                = Thread Int
type H                 = Horn ()
type Horns             = L H
type VCGenOutput       = (HornVariableMap, Horns)
type Substitutions     = HM.HashMap Id Int
type ModuleMap         = HM.HashMap Id (Module Int)
type ModuleInstanceMap = HM.HashMap Id (L (ModuleInstance Int))
type ExprPair          = (HornExpr, HornExpr)

newtype NextVars              = NextVars { _nextVars :: IM.IntMap Substitutions }
newtype HornVariableMap       = HornVariableMap { _getHornVariables :: IM.IntMap Ids }
newtype InitialEqualVariables = InitialEqualVariables { getInitialEqualVariables :: HM.HashMap Id Ids }

askHornVariables :: (Has (Reader HornVariableMap) sig m, MakeKVar t) => t Int -> m Ids
askHornVariables t = (IM.! getThreadId t) <$> asks _getHornVariables

getHornVariables :: (Has (State HornVariableMap) sig m, MakeKVar t) => t Int -> m Ids
getHornVariables t = (IM.! getThreadId t) <$> gets _getHornVariables

setHornVariables :: (Has (State HornVariableMap) sig m, MakeKVar t) => t Int -> Ids -> m ()
setHornVariables t vs = do
  HornVariableMap m <- get
  let m' = IM.insert (getThreadId t) vs m
  put $ HornVariableMap m'

alwaysEqualEqualities :: FDS sig m => TI -> m (L HornExpr)
alwaysEqualEqualities t = do
  Module {..} <- ask @M
  mNextVars <-
    case t of
      AB ab -> Just <$> getNextVars ab
      MI _ -> return Nothing
  let addEquals exprs v = exprs <> mkAEEquality v moduleName 0
  let go =
        case mNextVars of
          Nothing  -> addEquals
          Just nvs -> \exprs v ->
            let exprs' = addEquals exprs v
            in case HM.lookup v nvs of
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
getNextVars :: FD sig m => AlwaysBlock Int -> m Substitutions
getNextVars ab = do
  nextVarMap <- (IM.! getData ab) <$> asks _nextVars
  hornVars <- getHornVariables ab
  return $
    foldl'
    (\m v -> HM.insertWith (\_newIndex oldIndex -> oldIndex) v 0 m)
    nextVarMap hornVars


withAB :: FDM sig m => TI -> ReaderC ThreadSt m a -> m a
withAB t act = do
  threadSt :: ThreadSt  <- asks (IM.! getData t)
  act & runReader threadSt


computeThreadStM :: G' sig m => Module Int -> TI -> m ThreadSt
computeThreadStM m@Module{..} thread = do
  as <- getAnnotations moduleName
  let filterAs l = HS.intersection (as ^. l) vs
  wvs <- getUpdatedVariables thread
  extraInitEquals <- asks (hmGet 15 moduleName . getInitialEqualVariables)
  unless (HS.null extraInitEquals) $
    trace
    ("automatically added initial_equal annotations for wires of #" ++ show (getData thread))
    (sort $ toList extraInitEquals)
  let currentIEs =
        (filterAs initialEquals `HS.difference` inputs)
        <> extraInitEquals
  -- trace ("initial_eq of #" ++ show tid) (sort $ toList currentIEs)
  return $
    ThreadSt
    { _currentVariables     = vs
    , _currentSources       = filterAs sources
    , _currentSinks         = filterAs sinks
    , _currentInitialEquals = currentIEs
    , _currentAlwaysEquals  = filterAs alwaysEquals
    , _currentAssertEquals  = filterAs assertEquals
    , _currentWrittenVariables = wvs
    }
  where
    vs = getVariables thread
    inputs = moduleAllInputs m


data FDEQReadSt = FDEQReadSt
  { sccG      :: G.Gr IS.IntSet VarDepEdgeType
  , sccNodes  :: IM.IntMap Int
  , mInputs   :: Ids
  , mRegs     :: Ids
  , ms        :: ModuleSummary
  , m         :: Module Int
  }

type FDEQSt = HM.HashMap Id (Maybe FDEQReason)

data FDEQReason = FDEQReason
  { dependsOnInputs :: Ids
  , dependsOnReg    :: Ids
  , writtenByMI     :: HS.HashSet (Id, Id)
  }

type FDEQ sig m = ( G sig m
                  , Has (State FDEQSt) sig m
                  , Has (Reader FDEQReadSt) sig m
                  )

type IdsMap = HM.HashMap Id Ids

computeAllInitialEqualVars :: G sig m => L (Module Int) -> m IdsMap
computeAllInitialEqualVars modules = execState mempty $ for_ modules $ \m@Module{..} -> do
  reasons <- autoInitialEqualVars m
  ies <-
    execState (HS.empty :: Ids) $
    for_ (HM.toList reasons) $ \(v, mr) ->
    case mr of
      Nothing -> modify @Ids (HS.insert v)
      Just FDEQReason{..} ->
        if | notNull dependsOnInputs ->
               trace' "computeAllInitialEqualVars - dependsOnInputs" (moduleName, v, toList dependsOnInputs)
           | notNull dependsOnReg ->
               trace' "computeAllInitialEqualVars - dependsOnReg" (moduleName, v, toList dependsOnReg)
           | notNull writtenByMI -> do
               leftovers <-
                 flip filterM (toList writtenByMI) $ \(miType, miVar) ->
                 gets @IdsMap (notElem miVar . (HM.! miType))
               if null leftovers
                 then modify (HS.insert v)
                 else trace' "computeAllInitialEqualVars - writtenByMI" (moduleName, v, toList leftovers)
           | otherwise ->
             trace "computeAllInitialEqualVars - weird" (moduleName, v)
  modify @IdsMap (at moduleName ?~ ies)
  where
    notNull = not . HS.null
    trace' _ _ = return ()

autoInitialEqualVars :: G sig m => Module Int -> m FDEQSt
autoInitialEqualVars m@Module{..} = do
  ms@ModuleSummary{..} <- asks (hmGet 14 moduleName)
  let (sccG, toSCCNodeMap) = (variableDependenciesSCC, variableDependencySCCNodeMap)
      readSt =
        FDEQReadSt
        { sccG      = sccG
        , sccNodes  = toSCCNodeMap
        , mInputs   = moduleAllInputs m
        , mRegs     = allRegisters
        , ms        = ms
        , m         = m
        }
  for_ (G.topsort sccG) autoInitialEqualVarsRunSCCNode
    & runReader readSt
    & execState mempty
  where
    allRegisters =
      foldl' (\rs -> \case
                 Register{..} -> HS.insert variableName rs
                 Wire{} -> rs) mempty variables

autoInitialEqualVarsRunSCCNode :: FDEQ sig m => Int -> m ()
autoInitialEqualVarsRunSCCNode sccNode = do
  FDEQReadSt{..} <- ask
  let thisSCC = G.context sccG sccNode ^. _3
  for_ (IS.toList thisSCC)
    autoInitialEqualVarsRunOriginalNode

autoInitialEqualVarsRunOriginalNode :: FDEQ sig m => Int -> m (Maybe FDEQReason)
autoInitialEqualVarsRunOriginalNode n = do
  ModuleSummary{..} <- asks ms
  let toVar = (invVariableDependencyNodeMap IM.!)
      nName = toVar n
  mSt <- gets (HM.lookup nName)
  case mSt of
    Just st -> return st
    Nothing -> do
      currentModuleName <- asks (moduleName . m)
      as <- getAnnotations currentModuleName
      FDEQReadSt{..} <- ask
      let ies      = (as ^. initialEquals) <> (as ^. alwaysEquals)
          isIE     = nName `elem` ies
          isWire   = not . (`elem` mRegs)
          isIn     = nName `elem` mInputs
          nNameSet = HS.singleton nName
      st <-
        if | isIn -> return $ Just mempty {dependsOnInputs = nNameSet} -- variable is an input
           | isIE -> return Nothing -- variable is initial_eq
           | isWire nName ->
               case G.pre variableDependencies n of
                 [] ->
                   case HM.lookup nName threadWriteMap of
                     Nothing -> return $ Just mempty -- uninitialized variable
                     Just miId ->
                       case find ((== miId) . getData) (moduleInstances m) of
                         Nothing ->
                           return Nothing -- variable is initialized with constant value
                         Just ModuleInstance{..} -> do -- variable is written by a module instance
                           let miPorts = HM.toList moduleInstancePorts
                               miOutputLookup o = fst $ find' (eqVarName o . snd) miPorts
                               outputPort = miOutputLookup nName
                           return $ Just mempty {writtenByMI = HS.singleton (moduleInstanceType, outputPort)}
                 parents ->
                   mergeReasons
                   <$> traverse autoInitialEqualVarsRunOriginalNode parents
           | otherwise -> return $ Just mempty {dependsOnReg = nNameSet} -- variable is non-sanitized register
      modify @FDEQSt (at nName ?~ st)
      return st
  where
    eqVarName str = \case
      Variable{..} -> varName == str
      _ -> False

mergeReasons :: Foldable t => t (Maybe FDEQReason) -> Maybe FDEQReason
mergeReasons = foldl' go Nothing
  where
    go Nothing b = b
    go a Nothing = a
    go (Just a) (Just b) = Just (a <> b)


toSubs :: Id                    -- ^ module name
       -> Substitutions         -- ^ substitution map
       -> L ExprPair            -- ^ variable updates for the kvar
toSubs m = HM.foldlWithKey' go mempty
 where go subs v n = subs <> mkAllSubs v m 0 n


toSubsTags :: Id              -- ^ module name
           -> Substitutions   -- ^ substitution map
           -> L ExprPair      -- ^ variable updates for the kvar (for tags only)
toSubsTags m = HM.foldlWithKey' go mempty
 where go subs v n = subs <> mkTagSubs v m 0 n


-- | variable name -> module name -> lhs index -> rhs index -> horn variable
-- pairs for the equalities of vl, vr, tl, tr
mkAllSubs, mkTagSubs, mkValueSubs :: Id -> Id -> Int -> Int -> L ExprPair
mkAllSubs   v m n1 n2 = mkTagSubs v m n1 n2 <> mkValueSubs v m n1 n2
mkTagSubs   v m n1 n2 = (\r -> (HVar v m n1 Tag r 0,   HVar v m n2 Tag r 0))   <$> (LeftRun |:> RightRun)
mkValueSubs v m n1 n2 = (\r -> (HVar v m n1 Value r 0, HVar v m n2 Value r 0)) <$> (LeftRun |:> RightRun)


-- | creates a map between submodule names and all the instances of it
moduleInstancesMap :: L (Module Int) -> ModuleInstanceMap
moduleInstancesMap = foldl' handleModule mempty
  where
    handleModule miMap Module{..} = foldl' handleInstance miMap moduleInstances
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
    else do vars <- asks (^. currentVariables)
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

throw :: G sig m => String -> m a
throw = throwError . IE VCGen

getCurrentClocks :: FDM sig m => m Ids
getCurrentClocks = asks @M moduleName >>= getClocks

instance Semigroup FDEQReason where
  v1 <> v2 =
    FDEQReason
    { dependsOnInputs = dependsOnInputs v1 <> dependsOnInputs v2
    , dependsOnReg    = dependsOnReg v1 <> dependsOnReg v2
    , writtenByMI     = writtenByMI v1 <> writtenByMI v2
    }

instance Monoid FDEQReason where
  mempty = FDEQReason mempty mempty mempty

updateValues :: Foldable t => Int -> Id -> t Id -> L HornExpr
updateValues n moduleName =
  foldl' (\acc v -> acc <> (mkEqual <$> mkValueSubs v moduleName n 0)) mempty