{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

module Iodine.Transform.VCGen
  ( vcgen
  , VCGenOutput
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
import           Polysemy.Trace
-- import           Text.Printf


-- | State relevant to statements
data StmtSt = StmtSt { _currentVariables     :: Ids -- ^ all vars in this block

                     -- the rest is the filtered version of the Annotations type
                     , _currentSources       :: Ids
                     , _currentSinks         :: Ids
                     , _currentInitialEquals :: Ids
                     , _currentAlwaysEquals  :: Ids
                     , _currentAssertEquals  :: Ids
                     }
              deriving (Show)

makeLenses ''StmtSt

{- |
Verification condition generation creates the following 7 type of horn
constraints to encode our check:

1. Initialize: Encodes that initially, every tag is set to 0. We also encode
that the values of the variables that annotated as @initial_eq@ or @always_eq@
are the same. Keep in mind that @always_eq@ annotations apply to the rest of the
constraints listed below as well.

2. Tag Reset: The tags of the sources are set to 1, and the tags of the rest of
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

vcgenMod :: FD r => Module Int -> Sem r Horns
vcgenMod m@Module {..} = do
  annots <- getAnnotations moduleName
  assert (SQ.null gateStmts)
    "Gate statements should have been merged into always* blocks"
  assert singleBlockForEvent
    "There should be at most one always block for each event type"
  combine regularChecks alwaysBlocks
    <||> traverse instanceCheck moduleInstances
    <||> summaryConstraints m
    <||> interferenceChecks allStmts
    & runReader m
    & runReader annots
  where
    allStmts = (AB <$> alwaysBlocks) <> (MI <$> moduleInstances)
    allEvents = void <$> toList (abEvent <$> alwaysBlocks)
    singleBlockForEvent = length allEvents == length (nub allEvents)

regularChecks :: FDM r => AlwaysBlock Int -> Sem r Horns
regularChecks ab@AlwaysBlock{..} =
  withAB ab
  $    (SQ.singleton <$> initialize abStmt abEvent)
  ||>  tagReset abStmt abEvent
  ||>  srcTagReset abStmt abEvent
  ||>  next abStmt
  <||> sinkCheck abStmt
  <||> assertEqCheck abStmt


-- -------------------------------------------------------------------------------------------------
initialize :: FDS r => S -> Event Int -> Sem r (Horn ())
-- -------------------------------------------------------------------------------------------------
initialize stmt event = do
  m@Module {..} <- ask
  killNonTopModules m
  -- untag everything
  zeroTags <- foldl' (mkZeroTags moduleName) mempty <$> asks (^. currentVariables)
  -- init_eq and always_eq are initially set to the same values
  initEqs <- HS.union <$> asks (^. currentInitialEquals) <*> asks (^. currentAlwaysEquals)
  let initialCond = HAnd . fmap mkEqual $
                    foldl' (valEquals moduleName) zeroTags initEqs
  (initialCond', subs) <- case event of
    Star -> do
      nextSubs <- (toSubs moduleName) . (IM.! stmtId) <$> asks getNextVars
      return ( HAnd $ initialCond |:> transitionRelation stmt
             , nextSubs
             )
    _    -> return (initialCond, mempty)
  return $
    Horn { hornHead   = KVar stmtId subs
         , hornBody   = initialCond'
         , hornType   = Init
         , hornStmtId = stmtId
         , hornData   = ()
         }
 where
   stmtId = stmtData stmt
   mkZeroTags m subs v =
     subs |> (HVarTL0 v m, HBool False) |> (HVarTR0 v m, HBool False)
   valEquals m subs v =
     subs |> (HVarVL0 v m, HVarVR0 v m)


-- -------------------------------------------------------------------------------------------------
tagReset :: FDS r => S -> Event Int -> Sem r (Horn ())
-- -------------------------------------------------------------------------------------------------
tagReset stmt event = do
  m@Module {..} <- ask
  killNonTopModules m
  srcs <- getCurrentSources
  vars <- asks (^. currentVariables)
  let nonSrcs         = HS.difference vars srcs
      addModuleName v = (v, moduleName)
      tagsToSet       = addModuleName <$> toList srcs
      tagsToClear     = addModuleName <$> toList nonSrcs
      (eSet,   setSubs)   = updateTagsKeepValues True  tagsToSet
      (eClear, clearSubs) = updateTagsKeepValues False tagsToClear
      body = HAnd $ mkEmptyKVar stmtId <| eSet <> eClear
  (body', subs) <- case event of
    Star -> do
      aes <- alwaysEqualEqualities stmt
      nextVars  <- (HM.map (+ 1)) . (IM.! stmtId) <$> asks getNextVars
      let tr = indexFix $ transitionRelation stmt
      return ( HAnd $
               -- inv holds on 0 indices
               body           -- increment all indices, keep values but update tags
               |:> (HAnd $ indexFix <$> aes) -- always_eq on 1 indices and last hold
               |> tr                        -- transition starting from 1 indices
             , toSubsTags moduleName nextVars
             )
    _    ->
      return (body, setSubs <> clearSubs)
  return $
    Horn { hornHead   = KVar stmtId subs
         , hornBody   = body'
         , hornType   = TagReset
         , hornStmtId = stmtId
         , hornData   = ()
         }
  where
    updateTagsKeepValues b vs =
      foldl'
      (\(es, ss) (v, m) ->
         let es' = es
                   |> mkEqual (HVarTL v m 1, HBool b)
                   |> mkEqual (HVarTR v m 1, HBool b)
                   |> mkEqual (HVarVL v m 1, HVarVL0 v m)
                   |> mkEqual (HVarVR v m 1, HVarVR0 v m)
             ss' = ss
                   |> (HVarTL0 v m, HVarTL v m 1)
                   |> (HVarTR0 v m, HVarTR v m 1)
         in (es', ss'))
      (mempty, mempty) vs

    indexFix = updateIndices (+ 1)
    stmtId = stmtData stmt
{- HLINT ignore tagReset -}


-- -------------------------------------------------------------------------------------------------
srcTagReset :: FDS r => S -> Event Int -> Sem r (Horn ())
-- -------------------------------------------------------------------------------------------------
srcTagReset stmt event = do
  m@Module {..} <- ask
  killNonTopModules m
  srcs <- getCurrentSources
  vars <- asks (^. currentVariables)
  let addModuleName v = (v, moduleName)
      tagsToClear     = addModuleName <$> toList srcs
      (eClear, clearSubs) = updateTagsKeepValues False tagsToClear
      body = HAnd $ mkEmptyKVar stmtId <| eClear -- inv holds on 0 indices
  (body', subs) <- case event of
    Star -> do
      let nonSrcs = HS.difference vars srcs
      aes <- alwaysEqualEqualities stmt
      nextVars  <- (HM.map (+ 1)) . (IM.! stmtId) <$> asks getNextVars
      let tr = indexFix $ transitionRelation stmt
      return ( HAnd $
               body  -- increment indices of srcs, clear the tags of the sources but keep the values
               -- increment indices of non srcs, keep everything
               |:> (HAnd $ keepEverything $ addModuleName <$> toList nonSrcs)
               |> (HAnd $ indexFix <$> aes) -- always_eq on 1 indices and last hold
               |> tr -- transition starting from 1 indices
             , toSubsTags moduleName nextVars
             )
    _    ->
      return (body, clearSubs)
  return $
    Horn { hornHead   = KVar stmtId subs
         , hornBody   = body'
         , hornType   = TagReset
         , hornStmtId = stmtId
         , hornData   = ()
         }
  where
    keepEverything vs =
      foldl'
      (\es (v, m) ->
         es
         |> mkEqual (HVarVL v m 1, HVarVL0 v m)
         |> mkEqual (HVarVR v m 1, HVarVR0 v m)
         |> mkEqual (HVarTL v m 1, HVarTL0 v m)
         |> mkEqual (HVarTR v m 1, HVarTR0 v m))
      mempty vs

    updateTagsKeepValues b vs =
      foldl'
      (\(es, ss) (v, m) ->
         let es' = es
                   |> mkEqual (HVarTL v m 1, HBool b)
                   |> mkEqual (HVarTR v m 1, HBool b)
                   |> mkEqual (HVarVL v m 1, HVarVL0 v m)
                   |> mkEqual (HVarVR v m 1, HVarVR0 v m)
             ss' = ss
                   |> (HVarTL0 v m, HVarTL v m 1)
                   |> (HVarTR0 v m, HVarTR v m 1)
         in (es', ss'))
      (mempty, mempty) vs

    indexFix = updateIndices (+ 1)
    stmtId = stmtData stmt


-- -------------------------------------------------------------------------------------------------
next :: FDS r => S -> Sem r (Horn ())
-- -------------------------------------------------------------------------------------------------
next stmt = do
  m@Module {..} <- ask
  killNonTopModules m
  nextVars <- (IM.! stmtId) <$> asks getNextVars
  aes <- alwaysEqualEqualities stmt
  trace $ show ("equalities" :: String, aes)
  let subs = toSubs moduleName nextVars
  return $ Horn { hornBody   = HAnd $
                               (mkEmptyKVar stmtId <| aes) |>
                               transitionRelation stmt
                , hornHead   = KVar stmtId subs
                , hornType   = Next
                , hornStmtId = stmtId
                , hornData   = ()
                }
  where
    stmtId = stmtData stmt


-- -------------------------------------------------------------------------------------------------
sinkCheck :: FDS r => S -> Sem r Horns
-- -------------------------------------------------------------------------------------------------
sinkCheck stmt = do
  m@Module {..} <- ask
  killNonTopModules m
  snks <- asks (^. currentSinks)
  return $ foldl' (\hs v -> hs |> go moduleName v) mempty snks
 where
  stmtId = stmtData stmt
  go m v = Horn
    { hornHead   = HBinary HIff
                           (HVar v m 0 Tag LeftRun)
                           (HVar v m 0 Tag RightRun)
    , hornBody   = mkEmptyKVar stmtId
    , hornType   = TagEqual
    , hornStmtId = stmtId
    , hornData   = ()
    }


-- -------------------------------------------------------------------------------------------------
assertEqCheck :: FDS r => S -> Sem r Horns
-- -------------------------------------------------------------------------------------------------
assertEqCheck stmt = do
  m@Module {..} <- ask
  killNonTopModules m
  aes         <- asks (^. currentAssertEquals)
  return $ foldl' (\hs v -> hs |> go moduleName v) mempty aes
 where
  stmtId = stmtData stmt
  go m v = Horn
    { hornHead   = HBinary HEquals
                           (HVar v m 0 Value LeftRun)
                           (HVar v m 0 Value RightRun)
    , hornBody   = mkEmptyKVar stmtId
    , hornType   = AssertEqCheck
    , hornStmtId = stmtId
    , hornData   = ()
    }


-- -------------------------------------------------------------------------------------------------
instanceCheck :: FDM r => ModuleInstance Int -> Sem r (Horn ())
-- -------------------------------------------------------------------------------------------------
instanceCheck mi@ModuleInstance{..} = do
  PE.throw $ IE VCGen $ "module instances not supported yet"
  m@Module{..} <- asks @ModuleMap (HM.! moduleInstanceType)
  let subs =
        foldl'
        (\acc -> \case
            Input{..}  -> acc
            Output{..} ->
              let moduleVar = variableName portVariable
                  instanceVar = toHornVar (moduleInstancePorts HM.! moduleVar)
              in acc |>
                 ( instanceVar Tag LeftRun
                 , HVarTL0 moduleVar moduleInstanceType
                 ) |>
                 ( instanceVar Tag RightRun
                 , HVarTR0 moduleVar moduleInstanceType
                 ) |>
                 ( instanceVar Value LeftRun
                 , HVarVL0 moduleVar moduleInstanceType
                 ) |>
                 ( instanceVar Value RightRun
                 , HVarVR0 moduleVar moduleInstanceType
                 )
        )
        mempty
        ports
  return $
    Horn { hornHead   = KVar miId subs
         , hornBody   = mkEmptyKVar (getData m)
         , hornType   = InstanceCheck
         , hornStmtId = miId
         , hornData   = ()
         }
  where
    miId = getData mi


-- -------------------------------------------------------------------------------------------------
interferenceChecks :: FDM r => L TI -> Sem r Horns
-- -------------------------------------------------------------------------------------------------
interferenceChecks abmis =
  traverse_ interferenceCheck abmis
  & evalState @ICSts mempty
  & runState @Horns mempty
  & fmap fst

data ICSt = ICSt { icTI      :: TI
                 , writtenVars :: Ids
                 , allVars     :: Ids
                 , aeVars      :: Ids -- ^ always_eq vars
                 }
type ICSts = IM.IntMap ICSt

interferenceCheck :: (FDM r, Members '[State ICSts, State Horns] r)
                  => TI -> Sem r ()
interferenceCheck abmi = do
  -- traverse the statements we have looked at so far
  stmtSt <- computeStmtStM abmi
  currentWrittenVars <- getUpdatedVariables abmi
  let currentSt =
        ICSt { icTI      = abmi
             , writtenVars = currentWrittenVars
             , allVars     = currentAllVars
             , aeVars      = stmtSt ^. currentAlwaysEquals
             }
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
  modify $ IM.insert abmiId currentSt
 where
  abmiId = getData abmi
  currentAllVars = getVariables abmi

-- return the write/read interference check
interferenceCheckWR :: FDM r
                    => ICSt   -- ^ statement info that overwrites a variable
                    -> ICSt   -- ^ statement whose variable is being overwritten
                    -> Sem r (Horn ())
interferenceCheckWR wSt rSt = do
  Module {..} <- ask
  wNext <- (fromMaybe mempty) . (IM.lookup $ getData wTI) <$> asks getNextVars
  let rNext = HM.filterWithKey (\var _ -> HS.member var rVars) wNext
      mkAEs acc v =
        (case HM.lookup v rNext of
           Just n  -> acc
                      |> (HVarTL v moduleName n, HVarTR v moduleName n)
                      |> (HVarVL v moduleName n, HVarVR v moduleName n)
           Nothing -> acc)
        |> (HVarTL0 v moduleName, HVarTR0 v moduleName)
        |> (HVarVL0 v moduleName, HVarVR0 v moduleName)
      rAlwaysEqs = HS.foldl' mkAEs mempty (aeVars wSt `HS.union` aeVars rSt)
      subs = toSubs moduleName rNext
  return $
    Horn { hornHead   = KVar rId subs
         , hornBody   = HAnd
                        $   mkEmptyKVar rId
                        |:> mkEmptyKVar wId
                        |>  HAnd (mkEqual <$> rAlwaysEqs)
                        |>  wTR
         , hornType   = Interference
         , hornStmtId = wId
         , hornData   = ()
         }
  where
    rTI = icTI rSt
    wTI = icTI wSt
    rId   = getData rTI
    wId   = getData wTI
    rVars = allVars rSt

    wTR = case wTI of
            AB ab -> transitionRelation $ abStmt ab
            MI _  -> HBool True


-- -----------------------------------------------------------------------------
summaryConstraints :: G r => Module Int -> Sem r (L (Horn ()))
-- -----------------------------------------------------------------------------
summaryConstraints m@Module{..} = do
  ps <- getModulePorts m
  return $ case ps of
    SQ.Empty -> mempty
    _ -> SQ.singleton $
         Horn { hornHead   = mkEmptyKVar moduleData
              , hornBody   = HAnd threadKVars
              , hornType   = ModuleSummary
              , hornStmtId = moduleData
              , hornData   = ()
              }
  where
    threadKVars =
      (mkEmptyKVar . getData <$> alwaysBlocks)
      <> (mkEmptyKVar . getData <$> moduleInstances)

getModulePorts :: G r => Module Int -> Sem r (L Id)
getModulePorts Module{..} = do
  let portNames = variableName . portVariable <$> ports
  mClk <- getClock moduleName
  return $ (\v -> Just v /= mClk) `SQ.filter` portNames

-- summaryConstraints m = do
--   PE.throw $ IE VCGen $ "wip: summaryconstraints"
--   trace $ "summaryConstraints of " ++ show mn
--   mInstances <- getModuleInstances m
--   mClk <- getClock mn
--   case mInstances of
--     Nothing        -> return mempty
--     Just instances -> return . SQ.singleton $ summaryInitFromInstances mClk m instances
--   where
--     mn = moduleName m

-- -- | Values and tags of the expressions used in all the instances of the module
-- -- are used to initialize the input ports. Output ports' values and tags are
-- -- initially equal.
-- summaryInitFromInstances :: Maybe Id -> Module Int -> L (ModuleInstance Int) -> Horn ()
-- summaryInitFromInstances mClk m@Module{..} instances =
--   Horn { hornHead   = KVar mId (inputSubs <> outputSubs)
--        , hornBody   = body
--        , hornType   = ModuleSummary
--        , hornStmtId = mId
--        , hornData   = ()
--        }
--   where
--     body1 = instanceKVars instances
--     body2 =
--       mkEmptyKVar <$>
--       (getData <$> alwaysBlocks) <> (getData <$> moduleInstances)
--     body3 =
--       foldl' (\acc i -> acc <> instanceInputInitialValue instances i moduleName) mempty (inputs <> outputs)
--     body = HAnd $ body1 <> body2 <> body3
--     inputSubs = makeSubs inputs moduleName 1
--     outputSubs =
--       foldl' (\acc o -> acc |>
--                         (HVarVL0 o moduleName, HVarVR0 o moduleName) |>
--                         (HVarTL0 o moduleName, HVarTR0 o moduleName))
--       mempty outputs
--     mId     = getData m
--     inputs  = (\a -> Just a /= mClk) `SQ.filter` moduleInputs m
--     outputs = moduleOutputs m

-- instanceKVars :: L (ModuleInstance Int) -> L HornExpr
-- instanceKVars = fmap (mkEmptyKVar . getData)

-- -- | for each v in vs, add the v_0 <- v_n substitution for both tags and runs.
-- makeSubs :: Foldable f => f Id -> Id -> Int -> L (HornExpr, HornExpr)
-- makeSubs variables moduleName n =
--   foldl' (\acc v -> acc |>
--                     (HVarVL0 v moduleName, HVarVL v moduleName n) |>
--                     (HVarVR0 v moduleName, HVarVR v moduleName n) |>
--                     (HVarTL0 v moduleName, HVarTL v moduleName n) |>
--                     (HVarTR0 v moduleName, HVarTR v moduleName n))
--   mempty variables

-- instanceInputInitialValue :: L (ModuleInstance Int) -> Id -> Id -> L HornExpr
-- instanceInputInitialValue instances varName moduleName =
--   SQ.fromList $ do
--   t <- [Tag, Value]
--   r <- [LeftRun, RightRun]
--   let toExpr e = toHornVar e t r
--   case t of
--     Tag ->
--       return $
--       HBinary HIff
--       (HVar { hVarName   = varName
--             , hVarModule = moduleName
--             , hVarIndex  = 1
--             , hVarType   = t
--             , hVarRun    = r
--             })
--       (HOr $ toExpr . getInstanceVar varName <$> instances)
--     Value ->
--       return $
--       let hv = HVar { hVarName   = varName
--                    , hVarModule = moduleName
--                    , hVarIndex  = 1
--                    , hVarType   = t
--                    , hVarRun    = r
--                    }
--       in HOr (HBinary HEquals hv . toExpr . getInstanceVar varName <$> instances)
--   where
--     getInstanceVar v ModuleInstance{..} = moduleInstancePorts HM.! v

-- summaryNext :: Module Int -> Horn ()
-- summaryNext m@Module{..} =
--   Horn { hornHead   = KVar mId subs
--        , hornBody   = body
--        , hornType   = ModuleSummary
--        , hornStmtId = mId
--        , hornData   = ()
--        }
--   where
--     mn  = moduleName
--     mId = getData m
--     toSub v = SQ.fromList $ do
--       t <- [Tag, Value]
--       r <- [LeftRun, RightRun]
--       let e = HVar { hVarName   = v
--                    , hVarModule = mn
--                    , hVarIndex  = 0
--                    , hVarType   = t
--                    , hVarRun    = r
--                    }
--       return (e, e)
--     subs = mfold toSub (variableName . portVariable <$> ports)
--     body =
--       HAnd $
--       mkEmptyKVar <$>
--       (getData <$> alwaysBlocks) <> (getData <$> moduleInstances)

-- -----------------------------------------------------------------------------
-- Helper functions
-- -----------------------------------------------------------------------------

alwaysEqualEqualities :: FDS r => S -> Sem r (L HornExpr)
alwaysEqualEqualities stmt = do
  Module {..} <- ask
  nextVars <- (IM.! stmtId) <$> asks getNextVars
  foldl' (go moduleName nextVars) mempty <$> asks (^. currentAlwaysEquals)
  where
    stmtId = stmtData stmt
    go m nvs exprs v =
      let exprs' =
            exprs |>
            HBinary HEquals (HVarVL0 v m) (HVarVR0 v m) |>
            HBinary HIff    (HVarTL0 v m) (HVarTR0 v m)
      in case HM.lookup v nvs of
           Just n  -> exprs' |> HBinary HEquals (HVar v m n Value LeftRun) (HVar v m n Value RightRun)
           Nothing -> exprs'

type TI = Thread Int
type S = Stmt Int
type Horns = L (Horn ())

type VCGenOutput = Horns

type Substitutions = HM.HashMap Id Int
newtype NextVars = NextVars { getNextVars :: IM.IntMap Substitutions }

type ModuleMap = HM.HashMap Id (Module Int)
type G r = Members '[ Reader AnnotationFile
                    , PE.Error IodineException
                    , Trace
                    , Reader ModuleMap
                    ] r
-- FD  = global effects + next var map
type FD r  = ( G r
             , Members '[ Reader NextVars
                        , Reader ModuleInstanceMap
                        ] r)
type FDM r = (FD r,  Members '[Reader (Module Int)] r)  -- FDM = FD + current module
type FDS r = (FDM r, Members '[Reader StmtSt] r)        -- FDS = FDM + current statement state

withAB :: FDM r => AlwaysBlock Int -> Sem (Reader StmtSt ': r) a -> Sem r a
withAB ab act = do
  stmtSt <- computeStmtStM (AB ab)
  act & runReader stmtSt

computeStmtStM :: FDM r => TI -> Sem r StmtSt
computeStmtStM s = do
  m@Module{..} <- ask
  as  <- getAnnotations moduleName
  clk <- getClock moduleName
  return $ computeStmtSt clk as m s

computeStmtSt :: Maybe Id -> Annotations -> Module Int -> TI -> StmtSt
computeStmtSt mClk as Module{..} stmt =
  StmtSt
  { _currentVariables     = vs
  , _currentSources       = filterAs sources
  , _currentSinks         = filterAs sinks
  , _currentInitialEquals = HS.union extraInitEquals $ filterAs initialEquals
  , _currentAlwaysEquals  = filterAs alwaysEquals
  , _currentAssertEquals  = filterAs assertEquals
  }
  where
    filterAs l = HS.intersection (as ^. l) vs
    vs = getVariables stmt `HS.difference` maybeToSet mClk
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

maybeToSet :: Maybe Id -> HS.HashSet Id
maybeToSet Nothing  = mempty
maybeToSet (Just a) = HS.singleton a

getUpdatedVariables :: G r => TI -> Sem r Ids
getUpdatedVariables = \case
  AB ab -> go $ abStmt ab
  MI ModuleInstance{..} ->
   outputPorts <$> asks @ModuleMap (HM.! moduleInstanceType)
  where
    go = \case
      Block {..}      -> mfoldM go blockStmts
      Assignment {..} -> return . HS.singleton $ varName assignmentLhs
      IfStmt {..}     -> mfoldM go [ifStmtThen, ifStmtElse]
      Skip {..}       -> return mempty

toSubs :: Id                     -- ^ module name
       -> Substitutions          -- ^ substitution map
       -> L (HornExpr, HornExpr) -- ^ variable updates for the kvar
toSubs m = HM.foldlWithKey' go mempty
 where
  go subs v n =
    subs
      |> (HVar v m 0 Tag   LeftRun,  HVar v m n Tag   LeftRun)
      |> (HVar v m 0 Value LeftRun,  HVar v m n Value LeftRun)
      |> (HVar v m 0 Tag   RightRun, HVar v m n Tag   RightRun)
      |> (HVar v m 0 Value RightRun, HVar v m n Value RightRun)

toSubsTags :: Id                     -- ^ module name
           -> Substitutions          -- ^ substitution map
           -> L (HornExpr, HornExpr) -- ^ variable updates for the kvar (for tags only)
toSubsTags m = HM.foldlWithKey' go mempty
 where
  go subs v n =
    subs
      |> (HVar v m 0 Tag LeftRun,  HVar v m n Tag LeftRun)
      |> (HVar v m 0 Tag RightRun, HVar v m n Tag RightRun)

outputPorts :: Module a -> Ids
outputPorts Module{..} =
  foldl'
  (\xs -> \case
      Input{..}  -> xs
      Output{..} -> variableName portVariable `HS.insert` xs)
  mempty
  ports

type ModuleInstanceMap = HM.HashMap Id (L (ModuleInstance Int))

-- | creates a map between submodule names and all the instances of it
moduleInstancesMap :: L (Module Int) -> ModuleInstanceMap
moduleInstancesMap ir = foldl' handleModule mempty ir
  where
    handleModule miMap Module{..} = foldl' handleInstance miMap moduleInstances
    handleInstance miMap mi@ModuleInstance{..} =
      let mis' = case HM.lookup moduleInstanceType miMap of
                   Nothing  -> SQ.singleton mi
                   Just mis -> mis SQ.|> mi
      in HM.insert moduleInstanceType mis' miMap

mkEmptyKVar :: Int -> HornExpr
mkEmptyKVar n = KVar n mempty

isTopModule :: G r => Module Int -> Sem r Bool
isTopModule Module{..} = do
  topModuleName <- asks @AnnotationFile (^. afTopModule)
  return $ moduleName == topModuleName

-- getModuleInstances :: FD r => Module Int -> Sem r (Maybe (L (ModuleInstance Int)))
-- getModuleInstances m@Module{..} = do
--   (\c is -> if c then Nothing else Just is)
--     <$> isTopModule m
--     <*> asks @ModuleInstanceMap (HM.! moduleName)

getCurrentSources :: FDS r => Sem r Ids
getCurrentSources = do
  useAnnnotSources <- ask >>= isTopModule
  if useAnnnotSources
    then asks (^. currentSources)
    else do vars <- asks (^. currentVariables)
            inputs <- moduleInputs <$> ask
            return $ HS.filter (`elem` inputs) vars

killNonTopModules :: G r => Module Int -> Sem r ()
killNonTopModules m = do
  check <- isTopModule m
  unless check $ do
    PE.throw $ IE VCGen $ "wip: submodule instances"
