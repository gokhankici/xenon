{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

module Iodine.Transform.VCGen
  ( vcgen
  , VCGenOutput
  , HornVariableMap
  , askHornVariables
  )
where

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
  ThreadSt { _currentVariables     :: Ids -- ^ all vars in this block

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
  annots <- getAnnotations moduleName
  assert (SQ.null gateStmts)
    "Gate statements should have been merged into always* blocks"
  assert singleBlockForEvent
    "There should be at most one always block for each event type"
  mClk <- getClock moduleName
  isTop <- isTopModule' m
  setHornVariables m $ getVariables m `HS.difference` maybeToMonoid mClk
  for_ allThreads $ \t ->
    setHornVariables t $
    getVariables t <> if isTop then mempty else moduleInputs m mClk
  combine threadChecks allThreads
    <||> interferenceChecks allThreads
    <||> (maybeToMonoid <$> summaryConstraints m)
    & runReader m
    & runReader annots
    & runReader threadMap
  where
    allThreads          = moduleThreads m
    allEvents           = void <$> toList (abEvent <$> alwaysBlocks)
    singleBlockForEvent = length allEvents == length (nub allEvents)
    threadMap           = foldl' (\tm t -> IM.insert (getThreadId t) t tm) mempty allThreads

threadChecks :: FDM r => TI -> Sem r Horns
threadChecks thread =
  withAB thread
  $ (SQ.singleton <$> initialize thread)
  <||> let checks = tagSet |:> srcTagReset |> next
       in fmap catMaybes' (traverse ($ thread) checks)
  <||> sinkCheck thread
  <||> assertEqCheck thread


-- -------------------------------------------------------------------------------------------------
initialize, initializeTop, initializeSub :: FDS r => TI -> Sem r H
-- -------------------------------------------------------------------------------------------------
initialize thread = do
  top <- isTopModule
  if top
    then initializeTop thread
    else initializeSub thread

initializeTop thread@(AB _) = do
  Module{..} <- ask
  -- untag everything
  zeroTagSubs <- foldl' (mkZeroTags moduleName) mempty <$> asks (^. currentVariables)
  -- init_eq and always_eq are initially set to the same values
  initEqVars <- HS.union <$> asks (^. currentInitialEquals) <*> asks (^. currentAlwaysEquals)
  let initialCond = HAnd $ fmap mkEqual (foldl' (valEquals moduleName) mempty initEqVars)
  subs <-
    if   isStar thread
    then toSubs moduleName <$> getNextVars thread
    else return zeroTagSubs
  let extraConds = if   isStar thread
                   then fmap mkEqual zeroTagSubs |> transitionRelationT thread
                   else mempty
  return $
    Horn { hornHead   = makeKVar thread $
                        second setThreadId' <$> subs
         , hornBody   = setThreadId' $
                        HAnd $ initialCond <| extraConds
         , hornType   = Init
         , hornStmtId = getThreadId thread
         , hornData   = ()
         }
 where
   setThreadId' = setThreadId thread
   mkZeroTags m subs v =
     subs |> (HVarTL0 v m, HBool False) |> (HVarTR0 v m, HBool False)
   valEquals m subs v =
     subs |> (HVarVL0 v m, HVarVR0 v m)

initializeTop thread@(MI ModuleInstance{..}) = do
  currentModuleName <- asks moduleName
  targetModule <- asks (HM.! moduleInstanceType)
  alwaysEqVars <- asks (^. currentAlwaysEquals)
  let initEqs = setThreadId thread . mkEqual
                <$> foldl' (valEquals currentModuleName) mempty alwaysEqVars
      subs = second (setThreadId targetModule) <$>
             HM.foldlWithKey'
             (\acc portName portExpr ->
                acc <> mkSubs portExpr portName (moduleName targetModule))
             mempty
             moduleInstancePorts
  return $
    Horn { hornHead   = makeKVar thread subs
         , hornBody   = HAnd $ makeEmptyKVar targetModule <| initEqs
         , hornType   = Init
         , hornStmtId = getThreadId thread
         , hornData   = ()
         }
  where
    valEquals m subs v =
     subs |> (HVarVL0 v m, HVarVR0 v m)
    mkSubs kvarLhs kvarRhsName kvarRhsModule =
      mkSubsTR kvarLhs kvarRhsName kvarRhsModule <$> allTagRuns
    mkSubsTR kvarLhs kvarRhsName kvarRhsModule (t, r) =
      ( mkHornVar kvarLhs t r
      , mkHornVar (Variable kvarRhsName kvarRhsModule 0) t r
      )


initializeSub thread = do
  currentModule <- ask
  let currentModuleName = moduleName currentModule
  mClk <- getClock currentModuleName
  vars <- asks (^. currentVariables)
  let srcs    = moduleInputs currentModule mClk
      nonSrcs = vars `HS.difference` srcs

  let srcSubs    = second (setThreadId currentModule)
                   <$> foldMap (\v -> mkAllSubs v currentModuleName 0 0) srcs
  let nonSrcSubs = second (setThreadId thread)
                   <$> foldl' (mkZeroTags currentModuleName) mempty nonSrcs
  let subs       = srcSubs <> nonSrcSubs

  initEqVars <- HS.union <$> asks (^. currentInitialEquals) <*> asks (^. currentAlwaysEquals)
  let initEq = setThreadId thread
               <$> foldl' (valEquals currentModuleName) mempty initEqVars

  return $
    Horn { hornHead   = makeKVar thread subs
         , hornBody   = HAnd $ makeKVar currentModule mempty <| initEq
         , hornType   = Init
         , hornStmtId = getThreadId thread
         , hornData   = ()
         }
 where
   mkZeroTags m subs v =
     subs |> (HVarTL0 v m, HBool False) |> (HVarTR0 v m, HBool False)
   valEquals m eqs v = eqs |> mkEqual (HVarVL0 v m, HVarVR0 v m)


-- -------------------------------------------------------------------------------------------------
tagSet :: FDS r => TI -> Sem r (Maybe H)
-- -------------------------------------------------------------------------------------------------
tagSet thread = withTopModule $ do
  (Module {..}, srcs, vars) <- tagSetHelper
  let nonSrcs             = HS.difference vars srcs
      addModuleName v     = (v, moduleName)
      tagsToSet           = addModuleName <$> toList srcs
      tagsToClear         = addModuleName <$> toList nonSrcs
      (eSet,   setSubs)   = updateTagsKeepValues 1 True  tagsToSet
      (eClear, clearSubs) = updateTagsKeepValues 1 False tagsToClear
      body                = HAnd $ makeEmptyKVar thread <| eSet <> eClear
  (body', subs) <-
    if isStar thread
    then do
      aes      <- fmap (updateVarIndex (+ 1)) <$> alwaysEqualEqualities thread
      nextVars <- HM.map (+ 1) <$> getNextVars thread
      let tr = updateVarIndex (+ 1) $ transitionRelationT thread
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
      Horn { hornHead   = makeKVar thread $ second sti <$> subs
           , hornBody   = sti body'
           , hornType   = TagSet
           , hornStmtId = getThreadId thread
           , hornData   = ()
           }
  where
    sti = setThreadId thread
{- HLINT ignore tagSet -}

tagSetHelper :: FDS r => Sem r (Module Int, Ids, Ids)
tagSetHelper = (,,) <$> ask @(Module Int) <*> getCurrentSources <*> asks (^. currentVariables)


-- -------------------------------------------------------------------------------------------------
srcTagReset :: FDS r => TI -> Sem r (Maybe H)
-- -------------------------------------------------------------------------------------------------
srcTagReset thread = withTopModule $ do
  (Module {..}, srcs, vars) <- tagSetHelper
  let addModuleName v     = (v, moduleName)
      tagsToClear         = addModuleName <$> toList srcs
      (eClear, clearSubs) = updateTagsKeepValues 1 False tagsToClear
      -- increment indices of srcs, clear the tags of the sources but keep the values
      body = HAnd $ makeEmptyKVar thread <| eClear -- inv holds on 0 indices
  (body', subs) <-
    if isStar thread
    then do
      let nonSrcs = HS.difference vars srcs
          nonSrcUpdates = keepEverything 1 $ addModuleName <$> toList nonSrcs
      aes       <- fmap (updateVarIndex (+ 1)) <$> alwaysEqualEqualities thread
      nextVars  <- HM.map (+ 1) <$> getNextVars thread
      let tr    = updateVarIndex (+ 1) $ transitionRelationT thread
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
      Horn { hornHead   = makeKVar thread $ second sti <$> subs
           , hornBody   = sti body'
           , hornType   = SourceTagReset
           , hornStmtId = getThreadId thread
           , hornData   = ()
           }
  where
    sti = setThreadId thread
    keepEverything n =
      foldl' (\es (v, m) -> es <> (mkEqual <$> mkAllSubs v m n 0)) mempty

-- -------------------------------------------------------------------------------------------------
next :: FDS r => TI -> Sem r (Maybe H)
-- -------------------------------------------------------------------------------------------------
next (MI _) = return Nothing

next thread@(AB AlwaysBlock{..}) = do
  Module {..} <- ask
  nextVars    <- getNextVars thread
  aes         <- alwaysEqualEqualities thread
  trace "equalities" aes
  let subs  = second (setThreadId thread)
              <$> toSubs moduleName nextVars
  let threadKVar = makeEmptyKVar thread
  return . Just $
    Horn { hornBody   = setThreadId thread $ HAnd $
                        (threadKVar <| aes) |>
                        transitionRelation abStmt
         , hornHead   = makeKVar thread subs
         , hornType   = Next
         , hornStmtId = threadId
         , hornData   = ()
         }
  where
    threadId = getData thread


-- -------------------------------------------------------------------------------------------------
sinkCheck :: FDS r => TI -> Sem r Horns
-- -------------------------------------------------------------------------------------------------
sinkCheck thread = do
  Module {..} <- ask
  snks        <- asks (^. currentSinks)
  let threadKVar = makeEmptyKVar thread
  return $ foldl' (\hs v -> hs |> go threadKVar moduleName v) mempty snks
 where
  threadId = getData thread
  go threadKVar m v =
    Horn { hornHead   = setThreadId thread $
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
assertEqCheck thread = do
  Module {..} <- ask
  aes         <- asks (^. currentAssertEquals)
  let threadKVar = makeEmptyKVar thread
  return $ foldl' (\hs v -> hs |> go threadKVar moduleName v) mempty aes
 where
  threadId = getData thread
  go threadKVar m v =
    Horn { hornHead   = setThreadId thread $
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
  & evalState @ICSts mempty
  & runState @Horns mempty
  & fmap fst


data ICSt =
  ICSt { icTI        :: TI
       , writtenVars :: Ids
       , allVars     :: Ids
       , aeVars      :: Ids -- ^ always_eq vars
       }
type ICSts = IM.IntMap ICSt


interferenceCheck :: (FDM r, Members '[State ICSts, State Horns] r)
                  => TI -> Sem r ()
interferenceCheck thread   = do
  stmtSt  <- computeThreadStM thread
  currentWrittenVars <- getUpdatedVariables thread
  let currentAllVars = stmtSt ^. currentVariables
      currentSt =
        ICSt { icTI        = thread
             , writtenVars = currentWrittenVars
             , allVars     = currentAllVars
             , aeVars      = stmtSt ^. currentAlwaysEquals
             }
  -- traverse the statements we have looked at so far
  get @ICSts >>=
    traverse_
    (\icSt@ICSt {..} -> do
        -- if the current statement overwrites any variable that the previous
        -- statement uses ...
        when (currentWrittenVars `intersects` allVars) $ do
          h <- interferenceCheckWR currentSt icSt
          modify @Horns (|> h)
        -- if the previous statement overwrites any variable that the current
        -- statement uses ...
        when (writtenVars `intersects` currentAllVars) $ do
          h <- interferenceCheckWR icSt currentSt
          modify @Horns (|> h)
    )
  modify $ IM.insert threadId currentSt
 where threadId = getThreadId thread


-- return the write/read interference check
interferenceCheckWR :: FDM r
                    => ICSt   -- ^ statement info that overwrites a variable
                    -> ICSt   -- ^ statement whose variable is being overwritten
                    -> Sem r H
interferenceCheckWR wSt rSt = do
  Module {..} <- ask
  writeNext <- case writeThread of
                 AB _  -> getNextVars writeThread
                 MI mi -> do
                   let miType = moduleInstanceType mi
                   miModule <- asks @ModuleMap (HM.! miType)
                   miClk <- getClock miType
                   let os = moduleOutputs miModule miClk
                       lookupPortExpr o =
                         varName $ moduleInstancePorts mi HM.! o
                   return $ foldl' (\m o -> HM.insert (lookupPortExpr o) 0 m) mempty os
  let readNext = HM.filterWithKey (\var _ -> HS.member var readVars) writeNext
      mkAEs t acc v =
        let sti = setThreadId t
            fix = bimap sti sti
        in  (case HM.lookup v readNext of
               Just n  -> acc
                          |> fix (HVarTL v moduleName n, HVarTR v moduleName n)
                          |> fix (HVarVL v moduleName n, HVarVR v moduleName n)
               Nothing -> acc
            )
            |> fix (HVarTL0 v moduleName, HVarTR0 v moduleName)
            |> fix (HVarVL0 v moduleName, HVarVR0 v moduleName)
      readAlwaysEqs = HS.foldl' (mkAEs writeThread) mempty (aeVars wSt)
                      <> HS.foldl' (mkAEs readThread) mempty (aeVars rSt)
      subs = second (setThreadId writeThread)
             <$> toSubs moduleName readNext
  let readKVar  = makeEmptyKVar readThread
      writeKVar = makeEmptyKVar writeThread
  return $
    Horn { hornHead   = makeKVar readThread subs
         , hornBody   = HAnd
                        $   readKVar
                        |:> writeKVar
                        |>  HAnd (mkEqual <$> readAlwaysEqs)
                        |>  writeTR
         , hornType   = Interference
         , hornStmtId = writeId
         , hornData   = ()
         }
  where
    readThread  = icTI rSt
    writeThread = icTI wSt
    writeId     = getData writeThread
    readVars    = allVars rSt
    writeTR     = setThreadId writeThread $
                  transitionRelationT writeThread


-- -----------------------------------------------------------------------------
summaryConstraints :: FDM r => Module Int -> Sem r (Maybe H)
-- -----------------------------------------------------------------------------
summaryConstraints m@Module{..} = do
  mClk <- getClock moduleName
  let inputs = moduleInputs m mClk
  moduleHornVars <- getHornVariables m
  if HS.null moduleHornVars
    then return Nothing
    else do
    threadKVars <- fmap makeEmptyKVar <$> asks IM.elems
    -- calculate a map from variable name to list of thread indices
    -- HM.HashMap Id (L TI)
    varThreadMap <-
      fmap fst . runState @VarThreadMap mempty $
      for_ (moduleThreads m) $
      \t -> do let updateMap Nothing   = Just $ mempty |> t
                   updateMap (Just ts) = Just $ ts |> t
               getHornVariables t
                 >>= traverse_ (modify . HM.alter updateMap)
    let subs =
          foldMap (\v -> case HM.lookup v varThreadMap of
                           Just (t SQ.:<| _) -> second (setThreadId t)
                                                <$> mkAllSubs v moduleName 0 0
                           _ | v `HS.member` inputs -> mempty
                           _ -> error $ unlines [ "unreachable:"
                                                , show m
                                                , show varThreadMap
                                                , show moduleHornVars
                                                , show v
                                                ]
                  ) moduleHornVars
    return . Just $
      Horn { hornHead   = makeKVar m subs
           , hornBody   = HAnd $ SQ.fromList threadKVars
           , hornType   = ModuleSummary
           , hornStmtId = getData m
           , hornData   = ()
           }

type VarThreadMap = HM.HashMap Id (L TI)

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
                    ] r

-- | vcgen state  = global effects + next var map
type FD r  = ( G r
             , Members '[ Reader NextVars
                        , Reader ModuleInstanceMap
                        , State  HornVariableMap
                        ] r)

-- | module state = vcgen state + current module
type FDM r = ( FD r
             , Members '[ Reader (Module Int)
                        , Reader (IM.IntMap TI)
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
      AB _ -> Just <$> getNextVars t
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
getNextVars :: FD r => TI -> Sem r Substitutions
getNextVars t@(AB ab) = do
  nextVarMap <- (IM.! getData ab) <$> asks _nextVars
  hornVars <- getHornVariables t
  return $
    foldl'
    (\m v -> HM.insertWith (\_newIndex oldIndex -> oldIndex) v 0 m)
    nextVarMap hornVars
getNextVars (MI _)  = throw "getNextVars should be called with an always block!"


withAB :: FDM r => TI -> Sem (Reader ThreadSt ': r) a -> Sem r a
withAB t act = do
  stmtSt <- computeThreadStM t
  act & runReader stmtSt


computeThreadStM :: FDM r => TI -> Sem r ThreadSt
computeThreadStM t = do
  m@Module{..} <- ask
  as  <- getAnnotations moduleName
  return $ computeThreadSt as m t


computeThreadSt :: Annotations -> Module Int -> TI -> ThreadSt
computeThreadSt as Module{..} thread =
  ThreadSt
  { _currentVariables     = vs
  , _currentSources       = filterAs sources
  , _currentSinks         = filterAs sinks
  , _currentInitialEquals = HS.union extraInitEquals $ filterAs initialEquals
  , _currentAlwaysEquals  = filterAs alwaysEquals
  , _currentAssertEquals  = filterAs assertEquals
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
  MI ModuleInstance{..} -> do
    -- get the output ports of the module
    os <-
      moduleOutputs
      <$> asks @ModuleMap (HM.! moduleInstanceType)
      <*> getClock moduleInstanceType
    -- then, lookup the variables used for those ports
    let lukap = varName . (moduleInstancePorts HM.!)
    return $ foldl' (\acc -> mappend acc . liftToMonoid . lukap) mempty os
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
            inputs <- moduleInputs <$> ask <*> getCurrentClock
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

getCurrentClock :: FDM r => Sem r (Maybe Id)
getCurrentClock = asks moduleName >>= getClock
