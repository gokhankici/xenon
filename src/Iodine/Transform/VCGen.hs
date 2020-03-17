{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
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
  )
where

import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Transform.Horn
import           Iodine.Transform.Normalize (NormalizeOutput)
import           Iodine.Transform.TransitionRelation
import           Iodine.Types
import           Iodine.Utils

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
import           Data.List
import           Data.Maybe
import qualified Data.Sequence as SQ
import           Data.Traversable
import           Polysemy
import qualified Polysemy.Error as PE
import qualified Polysemy.Output as PO
import           Polysemy.Reader
import           Polysemy.State
import qualified Polysemy.Trace as PT

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
type G r = Members '[ Reader AnnotationFile
                    , PE.Error IodineException
                    , PT.Trace
                    , Reader ModuleMap
                    , Reader SummaryMap
                    , PO.Output String
                    ] r

-- | vcgen state  = global effects + next var map
type FD r  = ( G r
             , Members '[ Reader NextVars
                        , State  HornVariableMap
                        ] r)

-- | module state = vcgen state + current module
type FDM r = ( FD r
             , Members '[ Reader (Module Int)
                        , Reader (IM.IntMap TI)
                        , Reader (IM.IntMap ThreadSt)
                        ] r
             )

-- | stmt state = module state + current statement state
type FDS r = (FDM r, Members '[Reader ThreadSt] r)


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
vcgen :: G r => NormalizeOutput -> Sem r VCGenOutput
vcgen (ssaIR, trNextVariables) =
  combine vcgenMod ssaIR
  & runReader (NextVars trNextVariables)
  & runReader (moduleInstancesMap ssaIR)
  & runState  (HornVariableMap mempty)


vcgenMod :: FD r => Module Int -> Sem r Horns
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
  for_ alwaysBlocks $ \ab ->
    setHornVariables ab $
    getVariables ab <> if isTop then mempty else moduleInputs m mClks

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

moduleClauses :: FDM r => Sem r Horns
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

isModuleSimple :: Members '[ Reader AnnotationFile
                           , Reader SummaryMap
                           ] r
               => Module Int
               -> Sem r Bool
isModuleSimple m =
  (&&) <$> (not <$> isTopModule' m) <*> asks (isCombinatorial . hmGet 8 (moduleName m))

alwaysBlockClauses :: FDM r => AlwaysBlock Int -> Sem r Horns
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
initialize :: FDS r => AlwaysBlock Int -> Sem r H
-- -------------------------------------------------------------------------------------------------
initialize ab = do
  currentModule <- ask
  let currentModuleName = moduleName currentModule

  tagEqVars0 <- getHornVariables ab
  valEqVars0 <- HS.union <$> asks (^. currentInitialEquals) <*> asks (^. currentAlwaysEquals)

  isTop <- isTopModule
  srcs <- moduleInputs currentModule <$> getClocks currentModuleName
  let (tagEqVars, valEqVars) =
        if   isTop
        then (tagEqVars0, valEqVars0)
        else ( tagEqVars0 `HS.difference` srcs
             , valEqVars0 `HS.difference` srcs
             )

  trace ("initialize tag & val equalities #" ++ show (getData ab)) (toList tagEqVars, toList valEqVars)
  let tagSubs = sti2 <$> foldl' (mkZeroTags currentModuleName) mempty tagEqVars
      valSubs = sti2 <$> foldl' (valEquals currentModuleName) mempty valEqVars

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
                       else HM.filterWithKey (\v _ -> v `notElem` srcs) nxt
                subs = sti2 <$> toSubs currentModuleName nxt'
            return (HAnd (cond1 <> cond2 <> cond3 |> tr), subs)
    else return (HBool True, tagSubs <> valSubs)

  return $
    Horn { hornHead   = makeKVar ab subs
         , hornBody   = cond
         , hornType   = Init
         , hornStmtId = getThreadId ab
         , hornData   = ()
         }
 where
   sti = setThreadId ab
   sti2 = bimap sti sti
   uvi = updateVarIndex (+ 1)
   mkZeroTags m subs v =
     subs |> (HVarTL0 v m, HBool False) |> (HVarTR0 v m, HBool False)
   valEquals m subs v =
     subs |> (HVarVL0 v m, HVarVR0 v m)


combinatorialModuleInit :: FDM r => Sem r H
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
tagSet :: FDS r => AlwaysBlock Int -> Sem r (Maybe H)
-- -------------------------------------------------------------------------------------------------
tagSet ab = withTopModule $ do
  (Module {..}, srcs, vars) <- tagSetHelper
  let nonSrcs             = HS.difference vars srcs
      addModuleName v     = (v, moduleName)
      tagsToSet           = addModuleName <$> toList srcs
      tagsToClear         = addModuleName <$> toList nonSrcs
      (eSet,   setSubs)   = updateTagsKeepValues 1 True  tagsToSet
      (eClear, clearSubs) = updateTagsKeepValues 1 False tagsToClear
      body                = HAnd $ makeEmptyKVar ab <| eSet <> eClear
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

tagSetHelper :: FDS r => Sem r (Module Int, Ids, Ids)
tagSetHelper = (,,) <$> ask @(Module Int) <*> getCurrentSources <*> asks (^. currentVariables)


-- -------------------------------------------------------------------------------------------------
srcTagReset :: FDS r => AlwaysBlock Int -> Sem r (Maybe H)
-- -------------------------------------------------------------------------------------------------
srcTagReset ab = withTopModule $ do
  (Module {..}, srcs, vars) <- tagSetHelper
  let addModuleName v     = (v, moduleName)
      tagsToClear         = addModuleName <$> toList srcs
      (eClear, clearSubs) = updateTagsKeepValues 1 False tagsToClear
      -- increment indices of srcs, clear the tags of the sources but keep the values
      body = HAnd $ makeEmptyKVar ab <| eClear -- inv holds on 0 indices
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
next :: FDS r => AlwaysBlock Int -> Sem r H
-- -------------------------------------------------------------------------------------------------
next ab@AlwaysBlock{..} = do
  Module {..} <- ask
  nextVars    <- getNextVars ab
  aes         <- alwaysEqualEqualities thread
  -- trace "equalities" aes
  let subs  = second (setThreadId ab)
              <$> toSubs moduleName nextVars
  let threadKVar = makeEmptyKVar ab
  return $
    Horn { hornHead   = makeKVar ab subs
         , hornBody   = setThreadId ab $ HAnd $
                        (threadKVar <| aes) |>
                        transitionRelation abStmt
         , hornType   = Next
         , hornStmtId = threadId
         , hornData   = ()
         }
  where
    thread   = AB AlwaysBlock{..}
    threadId = getThreadId ab


-- -------------------------------------------------------------------------------------------------
sinkCheck :: FDS r => TI -> Sem r Horns
-- -------------------------------------------------------------------------------------------------
sinkCheck thread@(MI _) = do
  snks <- asks (^. currentSinks)
  writtenVars <- getUpdatedVariables thread
  unless (HS.null $ snks `HS.intersection` writtenVars) $
    throw "not implemented sink check of module instance outputs yet"
  return mempty

sinkCheck (AB ab) = do
  Module {..} <- ask
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
assertEqCheck :: FDS r => TI -> Sem r Horns
-- -------------------------------------------------------------------------------------------------
assertEqCheck thread@(MI _) = do
  snks <- asks (^. currentAssertEquals)
  writtenVars <- getUpdatedVariables thread
  unless (HS.null $ snks `HS.intersection` writtenVars) $
    throw "not implemented value assert check of module instance outputs yet"
  return mempty

assertEqCheck (AB ab) = do
  Module {..} <- ask
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
interferenceChecks :: FDM r => L TI -> Sem r Horns
-- -------------------------------------------------------------------------------------------------
interferenceChecks abmis =
  traverse_ interferenceCheck abmis
  & execState @Horns mempty

interferenceCheck :: (FDM r, Members '[State Horns] r)
                  => TI -> Sem r ()
interferenceCheck (MI _)  = return ()
interferenceCheck (AB readAB) = do
  Module{..} <- ask
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
    ( case writeThread of
        AB writeAB ->
          interferenceCheckAB writeAB readAB overlappingVars
        MI writeMI ->
          interferenceCheckMI writeMI readAB overlappingVars
      ) >>= \hornClause -> modify (SQ.|> hornClause)


interferenceCheckMI :: FDM r
                    => ModuleInstance Int -- ^ instance that does the update (writer)
                    -> AlwaysBlock Int    -- ^ always block being updated (reader)
                    -> Ids                -- ^ the variables being updated
                    -> Sem r H
interferenceCheckMI writeMI readAB overlappingVars = do
  m@Module{..} <- ask
  moduleSummary :: ModuleSummary <- asks (HM.! moduleName)
  depThreadIds <-
    IS.delete (getData readAB)
    <$> getAllDependencies (MI writeMI) & runReader moduleSummary
  depThreadInstances <-
    for (toSeq depThreadIds) $ \depThreadId -> do
    depThread <- asks (IM.! depThreadId)
    case depThread of
      AB depAB -> instantiateAB depAB overlappingVars
      MI depMI -> instantiateMI depMI
  readInstance <- instantiateAB readAB overlappingVars
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
  return $
    Horn { hornHead   = readHornHead
         , hornBody   = HAnd $
                        topModuleExprs <>
                        (depThreadInstances |> readInstance |> writeInstance)
                        <> readBodyExpr
         , hornType   = Interference
         , hornStmtId = getThreadId readAB
         , hornData   = ()
         }
  where
    toSeq = IS.foldl' (|>) SQ.empty


-- | return the interference check
interferenceCheckAB :: FDM r
                    => AlwaysBlock Int -- ^ always block that does the update (writer)
                    -> AlwaysBlock Int -- ^ always block being updated (reader)
                    -> Ids             -- ^ the variables being updated
                    -> Sem r H
interferenceCheckAB writeAB readAB overlappingVars= do
  currentModule <- ask @(Module Int)
  writeInstance <- instantiateAB writeAB mempty
  let sti     = setThreadId currentModule
      uvi1    = updateVarIndex (+ 1)
      writeTR = uvi1 $ sti $ transitionRelation (abStmt writeAB)
  writeNext <- HM.map (+ 1) <$> getNextVars writeAB
  (body, hd) <- interferenceReaderExpr readAB overlappingVars writeNext
  return $
    Horn { hornHead   = hd
         , hornBody   = HAnd $ writeInstance <| writeTR <| body
         , hornType   = Interference
         , hornStmtId = getThreadId readAB
         , hornData   = ()
         }

interferenceReaderExpr :: FDM r
                       => AlwaysBlock Int              -- ^ always block being updated (reader)
                       -> Ids                          -- ^ the variables being updated
                       -> Substitutions                -- ^ substitution map of the write thread
                       -> Sem r (L HornExpr, HornExpr) -- ^ body & head expression
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
                    Nothing -> extraSubs 1
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

moduleAlwaysEquals :: FDM r => Int -> Substitutions -> Sem r (L HornExpr)
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
instantiateAB :: FDM r => AlwaysBlock Int -> Ids -> Sem r HornExpr
instantiateAB ab excludedVars = do
  m@Module{..} <- ask
  let sti = setThreadId m
      mkInstance = fmap (second sti) . foldMap (\v -> mkAllSubs v moduleName 0 1)
  makeKVar ab . mkInstance . (`HS.difference` excludedVars) <$> getHornVariables ab


-- | instantiate the given module instance with variable index = 1 and thread
-- index equal to the current module's
instantiateMI :: FDM r => ModuleInstance Int -> Sem r HornExpr
instantiateMI mi = instantiateMI' mi 1

instantiateMI' :: FDM r => ModuleInstance Int -> Int -> Sem r HornExpr
instantiateMI' ModuleInstance{..} varIndex = do
  currentModule <- ask
  let currentModuleName = moduleName currentModule
  targetModule <- asks (hmGet 2 moduleInstanceType)
  let targetModuleName = moduleName targetModule
  targetModuleClocks <- getClocks moduleInstanceType
  let inputs  = moduleInputs targetModule targetModuleClocks
      outputs = moduleOutputs targetModule targetModuleClocks
      mkInputSubs i = do
        (t, f) <- (Value, val) |:> (Tag, tag)
        r <- LeftRun |:> RightRun
        return ( HVar0 i targetModuleName t r
               , updateVarIndex (const varIndex) $
                 f r $ hmGet 3 i moduleInstancePorts
               )
      mkOutputSubs o = do
        (t, r) <- allTagRuns
        let e = hmGet 4 o moduleInstancePorts
            rhs = if isVariable e
                  then HVar (varName e) currentModuleName varIndex t r 0
                  else error "output port expresssion of a module instance should be a variable"
        return ( HVar0 o targetModuleName t r
               , rhs
               )
      subs = second (setThreadId currentModule)
            <$> (foldMap mkInputSubs inputs <> foldMap mkOutputSubs outputs)
  return $ makeKVar targetModule subs

-- -----------------------------------------------------------------------------
summaryConstraint :: FDM r => Sem r H
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

instantiateAllThreads :: FDM r => Sem r HornExpr
instantiateAllThreads = do
  currentModule <- ask
  instances <-
    mappend
    <$> for (alwaysBlocks currentModule) (`instantiateAB` mempty)
    <*> traverse instantiateMI (moduleInstances currentModule)
  return $ HAnd instances

-- debuggingConstraints :: FDM r => Sem r Horns
-- debuggingConstraints = do
--   currentModule <- ask
--   case SQ.filter ((== 3) . getData) (moduleInstances currentModule) of
--     mi SQ.:<| _ -> do
--       trace "mi" mi
--       targetModule <- asks (`hmGet` moduleInstanceType mi)
--       let tmName = moduleName targetModule
--       let sti = setThreadId targetModule
--       let srcEq = mkEqual $
--                   bimap sti sti
--                   ( HVar "in2" tmName 0 Tag LeftRun 0
--                   , HVar "in2" tmName 0 Tag RightRun 0
--                   )
--       let outEq = mkEqual $
--                   bimap sti sti
--                   ( HVar "out2" tmName 0 Tag LeftRun 0
--                   , HVar "out2" tmName 0 Tag RightRun 0
--                   )
--       return . SQ.singleton $
--         Horn { hornHead   = outEq
--              , hornBody   = HAnd $ srcEq |:> makeEmptyKVar targetModule
--              , hornType   = TagEqual
--              , hornStmtId = getThreadId targetModule
--              , hornData   = ()
--              }
--     _ -> return mempty

-- -----------------------------------------------------------------------------
-- Helper functions
-- -----------------------------------------------------------------------------

type TI = Thread Int

type H = Horn ()

type Horns = L H

type VCGenOutput = (HornVariableMap, Horns)

type Substitutions = HM.HashMap Id Int

newtype NextVars = NextVars { _nextVars :: IM.IntMap Substitutions }

type ModuleMap = HM.HashMap Id (Module Int)

type ModuleInstanceMap = HM.HashMap Id (L (ModuleInstance Int))

type ExprPair = (HornExpr, HornExpr)

newtype HornVariableMap = HornVariableMap { _getHornVariables :: IM.IntMap Ids }

askHornVariables :: (Members '[Reader HornVariableMap] r, MakeKVar t) => t Int -> Sem r Ids
askHornVariables t = (IM.! getThreadId t) <$> asks _getHornVariables

getHornVariables :: (Members '[State HornVariableMap] r, MakeKVar t) => t Int -> Sem r Ids
getHornVariables t = (IM.! getThreadId t) <$> gets _getHornVariables

setHornVariables :: (Members '[State HornVariableMap] r, MakeKVar t) => t Int -> Ids -> Sem r ()
setHornVariables t vs = do
  HornVariableMap m <- get
  let m' = IM.insert (getThreadId t) vs m
  put $ HornVariableMap m'

alwaysEqualEqualities :: FDS r => TI -> Sem r (L HornExpr)
alwaysEqualEqualities t = do
  Module {..} <- ask
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
getNextVars :: FD r => AlwaysBlock Int -> Sem r Substitutions
getNextVars ab = do
  nextVarMap <- (IM.! getData ab) <$> asks _nextVars
  hornVars <- getHornVariables ab
  return $
    foldl'
    (\m v -> HM.insertWith (\_newIndex oldIndex -> oldIndex) v 0 m)
    nextVarMap hornVars


withAB :: FDM r => TI -> Sem (Reader ThreadSt ': r) a -> Sem r a
withAB t act = do
  threadSt :: ThreadSt  <- asks (IM.! getData t)
  act & runReader threadSt


computeThreadStM :: G r => Module Int -> TI -> Sem r ThreadSt
computeThreadStM m@Module{..} thread = do
  ms@ModuleSummary{..} <- asks (HM.! moduleName)
  as <- getAnnotations moduleName
  let allInitialEquals = HS.union (as ^. initialEquals) (as ^. alwaysEquals)
  let filterAs l = HS.intersection (as ^. l) vs
  wvs <- getUpdatedVariables thread
  let shouldAddWire w =
        let (dependsOnInput, requiredRegs) =
              computeRegistersWrittenBy m ms inputs w
            -- assume the wire is initial_eq if
            -- 1. the wire does not depend on module inputs
            -- 2. it's not a module instance output
            -- 3. all registers that it depends on are initial_eq
            cond1 = not dependsOnInput
            cond2 = ( not (null requiredRegs) ||
                      IS.null ((threadWriteMap HM.! w) `IS.intersection` miThreadIds))
            cond3 = all (`elem` allInitialEquals) requiredRegs
        in cond1 && cond2 && cond3
  let extraInitEquals =
        case thread of
          AB ab | not (isStar ab) ->
                  foldMap (\w -> if shouldAddWire w then HS.singleton w else mempty) currentWires
          _ -> mempty
  unless (HS.null extraInitEquals) $
    trace ("extraInitequals #" ++ show tid) (sort $ toList extraInitEquals)
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
    tid = getData thread
    miThreadIds = IS.fromList $ getData <$> toList moduleInstances
    vs = getVariables thread
    inputs =
      foldl'
      (\acc -> \case
          Input{..} -> HS.insert (variableName portVariable) acc
          Output{} -> acc
      ) mempty ports
    currentWires =
      foldl'
      (\ws -> \case
          Wire{..} ->
            if   variableName `elem` vs && variableName `notElem` inputs
            then ws SQ.|> variableName
            else ws
          Register{} -> ws
      ) mempty variables

-- | return the registers that write to the given wire
computeRegistersWrittenBy :: Module Int -> ModuleSummary -> Ids -> Id -> (Bool, Ids)
computeRegistersWrittenBy Module{..} ModuleSummary{..} inputs wireName =
  worklist (HS.singleton wireName) mempty (SQ.singleton wireName)
  where
    -- worklist :: wires that added to the worklist
    --          -> current set of registers
    --          -> worklist of wires
    --          -> registers
    worklist addedWires rs = \case
      SQ.Empty    -> (False, rs)
      w SQ.:<| ws ->
        let writtenNodes =
              G.pre variableDependencies (variableDependencyNodeMap HM.! w)
            (rs', foundWires) =
              foldl'
              (\acc n ->
                  let v = invVariableDependencyNodeMap IM.! n
                  in if v `elem` allRegisters
                     then acc & _1 %~ HS.insert v
                     else if w `elem` addedWires
                          then acc
                          else acc & _2 %~ HS.insert v
              )
              (rs, mempty)
              writtenNodes
            addedWires' = addedWires <> foundWires
            ws' = ws <> toSequence foundWires
        in if any (`elem` inputs) foundWires
           then (True, mempty)
           else worklist addedWires' rs' ws'

    allRegisters =
      foldl' (\rs -> \case
                 Register{..} -> HS.insert variableName rs
                 Wire{} -> rs) mempty variables

getUpdatedVariables :: G r => TI -> Sem r Ids
getUpdatedVariables = \case
  AB ab -> go $ abStmt ab
  MI mi@ModuleInstance{..} -> do
    (_, writtenVars) <-
      moduleInstanceReadsAndWrites
      <$> asks (hmGet 5 moduleInstanceType)
      <*> getClocks moduleInstanceType
      <*> return mi
    return writtenVars
  where
    go = \case
      Block {..}      -> mfoldM go blockStmts
      Assignment {..} -> return . HS.singleton $ varName assignmentLhs
      IfStmt {..}     -> mfoldM go [ifStmtThen, ifStmtElse]
      Skip {..}       -> return mempty


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


isTopModule :: Members '[Reader (Module Int),  Reader AnnotationFile] r => Sem r Bool
isTopModule = ask >>= isTopModule'

isTopModule' :: Members '[Reader AnnotationFile] r => Module a -> Sem r Bool
isTopModule' Module{..} = do
  topModuleName <- asks @AnnotationFile (^. afTopModule)
  return $ moduleName == topModuleName


withTopModule :: FDM r => Sem r (Maybe a) -> Sem r (Maybe a)
withTopModule act = do
  top <- isTopModule
  if top then act else return Nothing


getCurrentSources :: FDS r => Sem r Ids
getCurrentSources = do
  top <- isTopModule
  if top
    then asks (^. currentSources)
    else do vars <- asks (^. currentVariables)
            inputs <- moduleInputs <$> ask <*> getCurrentClocks
            return $ HS.filter (`elem` inputs) vars

updateTagsKeepValues :: Foldable t => Int -> Bool -> t (Id, Id) -> (L HornExpr, L ExprPair)
updateTagsKeepValues n b =
  foldl'
  (\(es, ss) (v, m) ->
     let es' = es
               -- <> (mkEqual <$> mkValueSubs v m n 0)
               |> mkEqual (HVarTL v m n, HBool b)
               |> mkEqual (HVarTR v m n, HBool b)
         ss' = ss <> mkTagSubs v m 0 n
     in (es', ss'))
  (mempty, mempty)

throw :: G r => String -> Sem r a
throw = PE.throw . IE VCGen

getCurrentClocks :: FDM r => Sem r Ids
getCurrentClocks = asks moduleName >>= getClocks

hmGet :: (Show k, Show v, Eq k, Hashable k)
      => Int -> k -> HM.HashMap k v -> v
hmGet n k m =
  case HM.lookup k m of
    Nothing ->
      error $ unlines [ "hashmap"
                      , show m
                      , "key " ++ show k
                      , "no " ++ show n
                      ]
    Just v -> v
