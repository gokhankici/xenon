{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Iodine.Transform.VCGen
  ( vcgen
  , VCGenOutput
  , HornVariableMap
  , askHornVariables
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

import qualified Data.Graph.Inductive as G
import           Control.Lens
import           Control.Monad
import           Data.Bifunctor
import           Data.Foldable
import           Data.Traversable
import           Data.Maybe
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntMap as IM
import           Data.List (nub)
import qualified Data.Sequence as SQ
import           Polysemy
import qualified Polysemy.Error as PE
import           Polysemy.Reader
import           Polysemy.State
import qualified Polysemy.Trace as PT


-- | State relevant to statements
data ThreadSt =
  ThreadSt { _currentVariables        :: Ids -- ^ all vars in this block
           , _currentWrittenVariables :: Ids

           -- the rest is the filtered version of the Annotations type
           , _currentSources       :: Ids
           , _currentSinks         :: Ids
           , _currentInitialEquals :: Ids
           , _currentAlwaysEquals  :: Ids
           , _currentAssertEquals  :: Ids

           }
  deriving (Show)

makeLenses ''ThreadSt

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
  mClks <- getClocks moduleName
  isTop <- isTopModule' m
  setHornVariables m $ getVariables m `HS.difference` mClks
  for_ alwaysBlocks $ \ab ->
    setHornVariables ab $
    getVariables ab <> if isTop then mempty else moduleInputs m mClks

  runReader m $ runReader threadMap $ do
    threadStMap :: IM.IntMap ThreadSt <-
      execState IM.empty $
      for allThreads $ \thread -> do
      threadSt  <- computeThreadStM m thread
      modify (IM.insert (getData thread) threadSt)

    runReader threadStMap $
      combine alwaysBlockClauses alwaysBlocks
      <||> combine (\mi -> let t = MI mi
                           in withAB t $
                              sinkCheck t <||> assertEqCheck t
                   ) moduleInstances
      <||> interferenceChecks allThreads
      <||> (SQ.singleton <$> summaryConstraint)
      <||> debuggingConstraints
  where
    allThreads          = (AB <$> alwaysBlocks) <> (MI <$> moduleInstances)
    allEvents           = void <$> toList (abEvent <$> alwaysBlocks)
    singleBlockForEvent = length allEvents == length (nub allEvents)
    threadMap           = foldl' (\tm t -> IM.insert (getData t) t tm) mempty allThreads

alwaysBlockClauses :: FDM r => AlwaysBlock Int -> Sem r Horns
alwaysBlockClauses ab =
  withAB t
  $ (SQ.singleton <$> initialize ab)
  <||> (maybeToMonoid <$> tagSet ab)
  <||> (maybeToMonoid <$> srcTagReset ab)
  ||>  next ab
  <||> sinkCheck t
  <||> assertEqCheck t
  where t = AB ab


-- -------------------------------------------------------------------------------------------------
initialize, initializeTop, initializeSub :: FDS r => AlwaysBlock Int -> Sem r H
-- -------------------------------------------------------------------------------------------------
initialize ab = do
  top <- isTopModule
  if top
    then initializeTop ab
    else initializeSub ab

initializeTop ab = do
  Module{..} <- ask
  -- untag everything
  zeroTagSubs <- foldl' (mkZeroTags moduleName) mempty <$> asks (^. currentVariables)
  -- init_eq and always_eq are initially set to the same values
  initEqVars <- HS.union <$> asks (^. currentInitialEquals) <*> asks (^. currentAlwaysEquals)
  let initialCond = HAnd $ fmap mkEqual (foldl' (valEquals moduleName) mempty initEqVars)
  subs <-
    if   isStar ab
    then toSubs moduleName <$> getNextVars ab
    else return zeroTagSubs
  let extraConds = if   isStar ab
                   then fmap mkEqual zeroTagSubs |> transitionRelation (abStmt ab)
                   else mempty
  return $
    Horn { hornHead   = makeKVar ab $
                        second setThreadId' <$> subs
         , hornBody   = setThreadId' $
                        HAnd $ initialCond <| extraConds
         , hornType   = Init
         , hornStmtId = getThreadId ab
         , hornData   = ()
         }
 where
   setThreadId' = setThreadId ab
   mkZeroTags m subs v =
     subs |> (HVarTL0 v m, HBool False) |> (HVarTR0 v m, HBool False)
   valEquals m subs v =
     subs |> (HVarVL0 v m, HVarVR0 v m)

initializeSub ab = do
  currentModule <- ask
  let currentModuleName = moduleName currentModule
  mClks <- getClocks currentModuleName
  vars <- asks (^. currentVariables)
  let srcs    = moduleInputs currentModule mClks
      nonSrcs = vars `HS.difference` srcs

  -- let srcSubs    = second (setThreadId currentModule)
  --                  <$> foldMap (\v -> mkAllSubs v currentModuleName 0 0) srcs
  let nonSrcSubs = second (setThreadId ab)
                   <$> foldl' (mkZeroTags currentModuleName) mempty nonSrcs
  -- let subs       = srcSubs <> nonSrcSubs

  initEqVars <- HS.union <$> asks (^. currentInitialEquals) <*> asks (^. currentAlwaysEquals)
  let initEq = setThreadId ab
               <$> foldl' (valEquals currentModuleName) mempty initEqVars

  return $
    Horn { hornHead   = makeKVar ab nonSrcSubs
         , hornBody   = HAnd initEq
         , hornType   = Init
         , hornStmtId = getThreadId ab
         , hornData   = ()
         }
 where
   mkZeroTags m subs v =
     subs |> (HVarTL0 v m, HBool False) |> (HVarTR0 v m, HBool False)
   valEquals m eqs v = eqs |> mkEqual (HVarVL0 v m, HVarVR0 v m)


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
  trace "equalities" aes
  let subs  = second (setThreadId ab)
              <$> toSubs moduleName nextVars
  let threadKVar = makeEmptyKVar ab
  return $
    Horn { hornBody   = setThreadId ab $ HAnd $
                        (threadKVar <| aes) |>
                        transitionRelation abStmt
         , hornHead   = makeKVar ab subs
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
interferenceCheck (AB ab) = do
  Module{..} <- ask
  ModuleSummary{..} <- asks (HM.! moduleName)
  trace "threadDependencies" threadDependencies
  unless (null $ G.pre threadDependencies $ getThreadId ab) $
    interferenceCheckWR ab

-- | return the interference check
interferenceCheckWR :: (FDM r, Members '[State Horns] r)
                    => AlwaysBlock Int
                    -> Sem r ()
interferenceCheckWR readAB = do
  currentModule <- ask @(Module Int)
  -- FIXME: add aeq of variables
  sourceTagEqs <- do
    isTop <- isTopModule
    if isTop
      then do let cmName = moduleName currentModule
              srcs <- getSources cmName
              let mkSrcEq v =
                    setThreadId currentModule $
                    mkEqual ( HVar v cmName 1 Tag LeftRun 0
                            , HVar v cmName 1 Tag RightRun 0
                            )
              return $
                foldl' (\acc v -> acc |> mkSrcEq v) mempty srcs
      else return mempty
  let currentModuleName = moduleName currentModule
  rSt :: ThreadSt <- asks (IM.! threadId)
  allInsts <- instantiateAllThreads (Just readAB)
  let readTr = setThreadId currentModule $
               updateVarIndex (+ 1) $
               transitionRelation $ abStmt readAB
  readNext <-  HM.map (+ 1) <$> getNextVars readAB
  let readSubs = second (setThreadId currentModule)
                 <$> toSubs currentModuleName readNext
      mkAEs v =
        let sti = setThreadId currentModule
            fix = bimap sti sti
            mn  = currentModuleName
        in  (case HM.lookup v readNext of
               Just n  -> fix (HVarTL v mn n, HVarTR v mn n)
                          |:> fix (HVarVL v mn n, HVarVR v mn n)
               Nothing -> mempty
            )
            |> fix (HVarTL v mn 1, HVarTR v mn 1)
            |> fix (HVarVL v mn 1, HVarVR v mn 1)
      readAlwaysEqs = foldMap mkAEs (rSt ^. currentAlwaysEquals)
  let hornClause =
        Horn { hornHead   = makeKVar readAB readSubs
             , hornBody   = HAnd $
                            (sourceTagEqs |> allInsts |> readTr)
                            <> (mkEqual <$> readAlwaysEqs)
             , hornType   = Interference
             , hornStmtId = threadId
             , hornData   = ()
             }
  modify (SQ.|> hornClause)
  where
    threadId = getThreadId readAB


-- | Instantiate all threads with variable index = 1 and thread index equal to
-- the current module's id. If an always block is given, the variables read by it
-- won't be used to instantiate it.
instantiateAllThreads :: FDM r
                      => Maybe (AlwaysBlock Int)
                      -> Sem r HornExpr
instantiateAllThreads mTargetAB = do
  currentModule <- ask
  let fixThreadId = setThreadId currentModule
  abInvs <-
    for (alwaysBlocks currentModule) $ \ ab -> do
    allHornParams <- getHornVariables ab
    hornParams <-
      case mTargetAB of
        Just targetAB
          | getThreadId ab == getThreadId targetAB ->
              asks (view currentWrittenVariables . (IM.! getThreadId targetAB))
        _ -> return allHornParams
    let mkEqs v = mkEqual . bimap (setThreadId ab) fixThreadId
                  <$> mkAllSubs v (moduleName currentModule) 0 1
        equalities = foldMap mkEqs hornParams
    return $ HAnd $ makeEmptyKVar ab <| equalities
  miInvs <- traverse instantiateModule (moduleInstances currentModule)
  return $ HAnd $ abInvs <> miInvs


-- | instantiate the given module instance with variable index = 1 and thread
-- index equal to the current module's
instantiateModule :: FDM r => ModuleInstance Int -> Sem r HornExpr
instantiateModule ModuleInstance{..} = do
  currentModule <- ask
  let currentModuleName = moduleName currentModule
  targetModule <- asks (HM.! moduleInstanceType)
  let targetModuleName = moduleName targetModule
  targetModuleClocks <- getClocks moduleInstanceType
  let inputs  = moduleInputs targetModule targetModuleClocks
      outputs = moduleOutputs targetModule targetModuleClocks
      mkInputSubs i = do
        (t, f) <- (Value, val) |:> (Tag, tag)
        r <- LeftRun |:> RightRun
        return ( HVar0 i targetModuleName t r
               , updateVarIndex (const 1) $
                 f r $ moduleInstancePorts HM.! i
               )
      mkOutputSubs o = do
        (t, r) <- allTagRuns
        let e = moduleInstancePorts HM.! o
            rhs = if isVariable e
                  then HVar (varName e) currentModuleName 1 t r 0
                  else error "output port expresssion of a module instance should be a variable"
        return ( HVar0 o targetModuleName t r
               , rhs
               )
      subs = bimap (setThreadId targetModule) (setThreadId currentModule) <$>
             (foldMap mkInputSubs inputs <> foldMap mkOutputSubs outputs)
  return $ HAnd $ makeEmptyKVar targetModule <| fmap mkEqual subs

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
  body <- instantiateAllThreads Nothing
  return $
    Horn { hornHead   = makeKVar m subs
         , hornBody   = body
         , hornType   = Summary
         , hornStmtId = getThreadId m
         , hornData   = ()
         }

debuggingConstraints :: FDM r => Sem r Horns
debuggingConstraints = do
  currentModule <- ask
  case SQ.filter ((== 3) . getData) (moduleInstances currentModule) of
    mi SQ.:<| _ -> do
      trace "mi" mi
      targetModule <- asks (HM.! moduleInstanceType mi)
      let tmName = moduleName targetModule
      let sti = setThreadId targetModule
      let srcEq = mkEqual $
                  bimap sti sti
                  ( HVar "in2" tmName 0 Tag LeftRun 0
                  , HVar "in2" tmName 0 Tag RightRun 0
                  )
      let outEq = mkEqual $
                  bimap sti sti
                  ( HVar "out2" tmName 0 Tag LeftRun 0
                  , HVar "out2" tmName 0 Tag RightRun 0
                  )
      return . SQ.singleton $
        Horn { hornHead   = outEq
             , hornBody   = HAnd $ srcEq |:> makeEmptyKVar targetModule
             , hornType   = TagEqual
             , hornStmtId = getThreadId targetModule
             , hornData   = ()
             }
    _ -> return mempty

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

-- | global state
type G r = Members '[ Reader AnnotationFile
                    , PE.Error IodineException
                    , PT.Trace
                    , Reader ModuleMap
                    , Reader SummaryMap
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
  let addEquals exprs v =
        exprs |>
        HBinary HEquals (HVarVL0 v moduleName) (HVarVR0 v moduleName) |>
        HBinary HIff    (HVarTL0 v moduleName) (HVarTR0 v moduleName)
  let go =
        case mNextVars of
          Nothing  -> addEquals
          Just nvs -> \exprs v ->
            let exprs' = addEquals exprs v
            in case HM.lookup v nvs of
              Just n  -> exprs' |>
                         HBinary HEquals
                         (HVar v moduleName n Value LeftRun 0)
                         (HVar v moduleName n Value RightRun 0)
              Nothing -> exprs'
  foldl' go mempty <$> asks (^. currentAlwaysEquals)


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
computeThreadStM m t = do
  as  <- getAnnotations (moduleName m)
  wvs <- getUpdatedVariables t
  return $ computeThreadSt as m t wvs


computeThreadSt :: Annotations -> Module Int -> TI -> Ids -> ThreadSt
computeThreadSt as Module{..} thread wvs =
  ThreadSt
  { _currentVariables     = vs
  , _currentSources       = filterAs sources
  , _currentSinks         = filterAs sinks
  , _currentInitialEquals = HS.union extraInitEquals $ filterAs initialEquals
  , _currentAlwaysEquals  = filterAs alwaysEquals
  , _currentAssertEquals  = filterAs assertEquals
  , _currentWrittenVariables = wvs
  }
  where
    vs = getVariables thread
    filterAs l = HS.intersection (as ^. l) vs
    extraInitEquals =
      foldl'
      (\vars -> \case
          w@Wire{..} ->
            if   isNothing $ Input w `SQ.elemIndexL` ports
            then HS.insert variableName vars
            else vars
          Register{..} ->
            vars)
      mempty
      variables


getUpdatedVariables :: G r => TI -> Sem r Ids
getUpdatedVariables = \case
  AB ab -> go $ abStmt ab
  MI mi@ModuleInstance{..} -> do
    (_, writtenVars) <-
      moduleInstanceReadsAndWrites
      <$> asks (HM.! moduleInstanceType)
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


isTopModule :: FDM r => Sem r Bool
isTopModule = ask >>= isTopModule'

isTopModule' :: G r => Module a -> Sem r Bool
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
               <> (mkEqual <$> mkValueSubs v m n 0)
               |> mkEqual (HVarTL v m n, HBool b)
               |> mkEqual (HVarTR v m n, HBool b)
         ss' = ss <> mkTagSubs v m 0 n
     in (es', ss'))
  (mempty, mempty)

throw :: G r => String -> Sem r a
throw = PE.throw . IE VCGen

trace :: (Members '[PT.Trace] r, Show a) => String -> a -> Sem r ()
trace msg a = do
  PT.trace msg
  PT.trace $ show a

getCurrentClocks :: FDM r => Sem r Ids
getCurrentClocks = asks moduleName >>= getClocks
