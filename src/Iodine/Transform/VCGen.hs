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


vcgenMod :: FD r => Module Int -> Sem r Horns
vcgenMod m@Module {..} = do
  annots <- getAnnotations moduleName
  assert (SQ.null gateStmts)
    "Gate statements should have been merged into always* blocks"
  assert singleBlockForEvent
    "There should be at most one always block for each event type"
  combine threadChecks allThreads
    <||> (maybeToMonoid <$> summaryConstraints m)
    <||> interferenceChecks allThreads
    & runReader m
    & runReader annots
  where
    allThreads          = (AB <$> alwaysBlocks) <> (MI <$> moduleInstances)
    allEvents           = void <$> toList (abEvent <$> alwaysBlocks)
    singleBlockForEvent = length allEvents == length (nub allEvents)


threadChecks :: FDM r => TI -> Sem r Horns
threadChecks thread =
  withAB thread
  $ (SQ.singleton <$> initialize thread)
  <||> fmap catMaybes' (traverse ($ thread) (tagSet |:> srcTagReset |> next))
  <||> sinkCheck thread
  <||> assertEqCheck thread


-- -------------------------------------------------------------------------------------------------
initialize :: FDS r => TI -> Sem r H
-- -------------------------------------------------------------------------------------------------
initialize thread@(AB _) = do
  Module{..} <- ask
  -- untag everything
  zeroTags   <- foldl' (mkZeroTags moduleName) mempty <$> asks (^. currentVariables)
  -- init_eq and always_eq are initially set to the same values
  initEqs    <- HS.union <$> asks (^. currentInitialEquals) <*> asks (^. currentAlwaysEquals)
  let initialCond = HAnd $
                    fmap mkEqual (foldl' (valEquals moduleName) zeroTags initEqs)
                    |> transitionRelationT thread
  subs <-
    if isStar thread
    then toSubs moduleName <$> getNextVars thread
    else return mempty
  return $
    Horn { hornHead   = KVar threadId subs
         , hornBody   = initialCond
         , hornType   = Init
         , hornStmtId = threadId
         , hornData   = ()
         }
 where
   threadId = getData thread
   mkZeroTags m subs v =
     subs |> (HVarTL0 v m, HBool False) |> (HVarTR0 v m, HBool False)
   valEquals m subs v =
     subs |> (HVarVL0 v m, HVarVR0 v m)


initialize thread@(MI ModuleInstance{..}) = do
  mn           <- asks moduleName
  targetModule <- asks (HM.! moduleInstanceType)
  initEqVars   <- HS.union <$> asks (^. currentInitialEquals) <*> asks (^. currentAlwaysEquals)
  let initEqs = mkEqual <$> foldl' (valEquals mn) mempty initEqVars
      initialCond = HAnd $ mkEmptyKVar (getData targetModule) <| initEqs
      subs        = HM.foldlWithKey'
             (\acc p e -> acc <> mkAllSubs e p (moduleName targetModule))
             mempty
             moduleInstancePorts
  return $
    Horn { hornHead   = KVar threadId subs
         , hornBody   = initialCond
         , hornType   = Init
         , hornStmtId = threadId
         , hornData   = ()
         }
  where
    threadId = getData thread
    valEquals m subs v =
     subs |> (HVarVL0 v m, HVarVR0 v m)
    mkAllSubs kvarLhs kvarRhsName kvarRhsModule =
      mkAllSubsTR kvarLhs kvarRhsName kvarRhsModule <$> allTagRuns
    mkAllSubsTR kvarLhs kvarRhsName kvarRhsModule (t, r) =
      ( mkHornVar kvarLhs t r
      , mkHornVar (Variable kvarRhsName kvarRhsModule 0) t r
      )


-- -------------------------------------------------------------------------------------------------
tagSet :: FDS r => TI -> Sem r (Maybe H)
-- -------------------------------------------------------------------------------------------------
tagSet thread = withTopModule $ do
  Module {..} <- ask
  killNonTopModules
  srcs <- getCurrentSources
  vars <- asks (^. currentVariables)
  let nonSrcs             = HS.difference vars srcs
      addModuleName v     = (v, moduleName)
      tagsToSet           = addModuleName <$> toList srcs
      tagsToClear         = addModuleName <$> toList nonSrcs
      (eSet,   setSubs)   = updateTagsKeepValues 1 True  tagsToSet
      (eClear, clearSubs) = updateTagsKeepValues 1 False tagsToClear
      body                = HAnd $ mkEmptyKVar threadId <| eSet <> eClear
  (body', subs) <-
    if isStar thread
    then do
      aes      <- alwaysEqualEqualities thread
      nextVars <- HM.map (+ 1) <$> getNextVars thread
      let tr = indexFix $ transitionRelationT thread
      return ( HAnd $
               -- inv holds on 0 indices
               body        -- increment all indices, keep values but update tags
               |:> HAnd (indexFix <$> aes) -- always_eq on 1 indices and last hold
               |> tr                       -- transition starting from 1 indices
             , toSubsTags moduleName nextVars
             )
    else return (body, setSubs <> clearSubs)
  return $
    Horn { hornHead   = KVar threadId subs
         , hornBody   = body'
         , hornType   = TagReset
         , hornStmtId = threadId
         , hornData   = ()
         }
  where
    indexFix = updateIndices (+ 1)
    threadId = getData thread


-- -------------------------------------------------------------------------------------------------
srcTagReset :: FDS r => TI -> Sem r (Maybe H)
-- -------------------------------------------------------------------------------------------------
srcTagReset thread = withTopModule $ do
  Module {..} <- ask
  srcs <- getCurrentSources
  vars <- asks (^. currentVariables)
  let addModuleName v     = (v, moduleName)
      tagsToClear         = addModuleName <$> toList srcs
      (eClear, clearSubs) = updateTagsKeepValues 1 False tagsToClear
      body                = HAnd $ mkEmptyKVar threadId <| eClear -- inv holds on 0 indices
  (body', subs) <-
    if isStar thread
    then do
      let nonSrcs = HS.difference vars srcs
      aes       <- alwaysEqualEqualities thread
      nextVars  <- HM.map (+ 1) <$> getNextVars thread
      let tr    = indexFix $ transitionRelationT thread
          body' = body  -- increment indices of srcs, clear the tags of the sources but keep the values
                  -- increment indices of non srcs, keep everything
                  |:> HAnd (keepEverything 1 $ addModuleName <$> toList nonSrcs)
                  |> HAnd (indexFix <$> aes) -- always_eq on 1 indices and last hold
                  |> tr -- transition starting from 1 indices
      return (HAnd body', toSubsTags moduleName nextVars)
    else return (body, clearSubs)
  return $
    Horn { hornHead   = KVar threadId subs
         , hornBody   = body'
         , hornType   = TagReset
         , hornStmtId = threadId
         , hornData   = ()
         }
  where
    indexFix = updateIndices (+ 1)
    threadId = getData thread


-- -------------------------------------------------------------------------------------------------
next :: FDS r => TI -> Sem r (Maybe H)
-- -------------------------------------------------------------------------------------------------
next (MI _) = return Nothing

next thread@(AB AlwaysBlock{..}) = do
  Module {..} <- ask
  nextVars      <- getNextVars thread
  aes           <- alwaysEqualEqualities thread
  trace $ show ("equalities" :: String, aes)
  let subs                       = toSubs moduleName nextVars
  return . Just $
    Horn { hornBody              = HAnd $
                        (mkEmptyKVar threadId <| aes) |>
                        transitionRelation abStmt
         , hornHead              = KVar threadId subs
         , hornType              = Next
         , hornStmtId            = threadId
         , hornData              = ()
         }
  where
    threadId = getData thread




-- -------------------------------------------------------------------------------------------------
sinkCheck :: FDS r => TI -> Sem r Horns
-- -------------------------------------------------------------------------------------------------
sinkCheck thread = do
  Module {..} <- ask
  snks          <- asks (^. currentSinks)
  return $ foldl' (\hs v -> hs |> go moduleName v) mempty snks
 where
  threadId       = getData thread
  go m v         = Horn
    { hornHead   = HBinary HIff
                           (HVar v m 0 Tag LeftRun)
                           (HVar v m 0 Tag RightRun)
    , hornBody   = mkEmptyKVar threadId
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
  return $ foldl' (\hs v -> hs |> go moduleName v) mempty aes
 where
  threadId = getData thread
  go m v = Horn
    { hornHead   = HBinary HEquals
                           (HVar v m 0 Value LeftRun)
                           (HVar v m 0 Value RightRun)
    , hornBody   = mkEmptyKVar threadId
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
 where threadId = getData thread


-- return the write/read interference check
interferenceCheckWR :: FDM r
                    => ICSt   -- ^ statement info that overwrites a variable
                    -> ICSt   -- ^ statement whose variable is being overwritten
                    -> Sem r H
interferenceCheckWR wSt rSt = do
  Module {..} <- ask
  writeNext <- case writeThread of
                 AB _ -> getNextVars writeThread
                 MI _ -> return mempty
  let readNext = HM.filterWithKey (\var _ -> HS.member var readVars) writeNext
      mkAEs acc v =
        (case HM.lookup v readNext of
           Just n  -> acc
                      |> (HVarTL v moduleName n, HVarTR v moduleName n)
                      |> (HVarVL v moduleName n, HVarVR v moduleName n)
           Nothing -> acc
        )
        |> (HVarTL0 v moduleName, HVarTR0 v moduleName)
        |> (HVarVL0 v moduleName, HVarVR0 v moduleName)
      readAlwaysEqs = HS.foldl' mkAEs mempty (aeVars wSt `HS.union` aeVars rSt)
      subs = toSubs moduleName readNext
  return $
    Horn { hornHead   = KVar readId subs
         , hornBody   = HAnd
                        $   mkEmptyKVar readId
                        |:> mkEmptyKVar writeId
                        |>  HAnd (mkEqual <$> readAlwaysEqs)
                        |>  writeTR
         , hornType   = Interference
         , hornStmtId = writeId
         , hornData   = ()
         }
  where
    readThread  = icTI rSt
    writeThread = icTI wSt
    readId      = getData readThread
    writeId     = getData writeThread
    readVars    = allVars rSt
    writeTR     = transitionRelationT writeThread


-- -----------------------------------------------------------------------------
summaryConstraints :: G r => Module Int -> Sem r (Maybe H)
-- -----------------------------------------------------------------------------
summaryConstraints m@Module{..} = do
  ps <- getModulePorts m
  return $ case ps of
    SQ.Empty -> Nothing
    _ -> Just $
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


-- -----------------------------------------------------------------------------
-- Helper functions
-- -----------------------------------------------------------------------------

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
                         (HVar v moduleName n Value LeftRun)
                         (HVar v moduleName n Value RightRun)
              Nothing -> exprs'
  foldl' go mempty <$> asks (^. currentAlwaysEquals)

type TI = Thread Int
type H = Horn ()
type Horns = L H

type VCGenOutput = Horns

type Substitutions = HM.HashMap Id Int
newtype NextVars = NextVars { _nextVars :: IM.IntMap Substitutions }

-- | get the last index of each variable after transitioning from variables with
-- index 0
getNextVars :: FD r => TI -> Sem r Substitutions
getNextVars (AB ab) = (IM.! getData ab) <$> asks _nextVars
getNextVars (MI _)  = throw "getNextVars should be called with an always block!"

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
type FDS r = (FDM r, Members '[Reader ThreadSt] r)         -- FDS = FDM + current statement state

withAB :: FDM r => TI -> Sem (Reader ThreadSt ': r) a -> Sem r a
withAB t act = do
  stmtSt <- computeThreadStM t
  act & runReader stmtSt

computeThreadStM :: FDM r => TI -> Sem r ThreadSt
computeThreadStM t = do
  m@Module{..} <- ask
  as  <- getAnnotations moduleName
  clk <- getClock moduleName
  return $ computeThreadSt clk as m t

computeThreadSt :: Maybe Id -> Annotations -> Module Int -> TI -> ThreadSt
computeThreadSt mClk as Module{..} t =
  ThreadSt
  { _currentVariables     = vs
  , _currentSources       = filterAs sources
  , _currentSinks         = filterAs sinks
  , _currentInitialEquals = HS.union extraInitEquals $ filterAs initialEquals
  , _currentAlwaysEquals  = filterAs alwaysEquals
  , _currentAssertEquals  = filterAs assertEquals
  }
  where
    filterAs l = HS.intersection (as ^. l) vs
    vs = getVariables t `HS.difference` maybeToSet mClk
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
  MI ModuleInstance{..} -> do
    -- get the output ports of the module
    ps <- outputPorts <$> asks @ModuleMap (HM.! moduleInstanceType)
    -- then, lookup the variables used for those ports
    return $ HS.map (varName . (moduleInstancePorts HM.!)) ps
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
moduleInstancesMap = foldl' handleModule mempty
  where
    handleModule miMap Module{..} = foldl' handleInstance miMap moduleInstances
    handleInstance miMap mi@ModuleInstance{..} =
      let mis' = case HM.lookup moduleInstanceType miMap of
                   Nothing  -> SQ.singleton mi
                   Just mis -> mis SQ.|> mi
      in HM.insert moduleInstanceType mis' miMap

mkEmptyKVar :: Int -> HornExpr
mkEmptyKVar n = KVar n mempty

isTopModule :: FDM r => Sem r Bool
isTopModule = do
  Module{..} <- ask
  topModuleName <- asks @AnnotationFile (^. afTopModule)
  return $ moduleName == topModuleName

withTopModule :: FDM r => Sem r a -> Sem r (Maybe a)
withTopModule act = do
  top <- isTopModule
  if top then Just <$> act else return Nothing

getCurrentSources :: FDS r => Sem r Ids
getCurrentSources = do
  useAnnnotSources <- isTopModule
  if useAnnnotSources
    then asks (^. currentSources)
    else do vars <- asks (^. currentVariables)
            inputs <- moduleInputs <$> ask
            return $ HS.filter (`elem` inputs) vars

killNonTopModules :: FDM r => Sem r ()
killNonTopModules = do
  check <- isTopModule
  unless check $ throw "wip: submodule instances"

transitionRelationT :: TI -> HornExpr
transitionRelationT (AB ab) = transitionRelation $ abStmt ab
transitionRelationT (MI _)  = HBool True

maybeToMonoid :: (Snoc m m a a, Monoid m) => Maybe a -> m
maybeToMonoid (Just a) = mempty |> a
maybeToMonoid Nothing  = mempty

-- | is the given thread an always block with the star event?
isStar :: TI -> Bool
isStar (AB ab) = abEvent ab == Star
isStar (MI _)  = False

throw :: G r => String -> Sem r a
throw = PE.throw . IE VCGen

mkHornVar :: Expr Int -> HornVarType -> HornVarRun -> HornExpr
mkHornVar Variable{..} t r =
  HVar { hVarName   = varName
       , hVarModule = varModuleName
       , hVarIndex  = exprData
       , hVarType   = t
       , hVarRun    = r
       }
mkHornVar _ _ _ =
  error "mkHornVar must be called with an IR variable"

allTagRuns :: L (HornVarType, HornVarRun)
allTagRuns =
  mempty |>
  (Value, LeftRun) |>
  (Value, RightRun) |>
  (Tag,   LeftRun) |>
  (Tag,   RightRun)


keepEverything :: (Foldable t, Snoc s s HornExpr HornExpr, Monoid s)
               => Int -> t (Id, Id) -> s
keepEverything n =
  foldl'
  (\es (v, m) ->
     es
     |> mkEqual (HVarVL v m n, HVarVL0 v m)
     |> mkEqual (HVarVR v m n, HVarVR0 v m)
     |> mkEqual (HVarTL v m n, HVarTL0 v m)
     |> mkEqual (HVarTR v m n, HVarTR0 v m))
  mempty

updateTagsKeepValues :: ( Foldable t, Monoid a, Monoid b
                        , Snoc b b (HornExpr, HornExpr) (HornExpr, HornExpr)
                        , Snoc a a HornExpr HornExpr)
                     => Int -> Bool -> t (Id, Id) -> (a, b)
updateTagsKeepValues n b =
  foldl'
  (\(es, ss) (v, m) ->
     let es' = es
               |> mkEqual (HVarTL v m n, HBool b)
               |> mkEqual (HVarTR v m n, HBool b)
               |> mkEqual (HVarVL v m n, HVarVL0 v m)
               |> mkEqual (HVarVR v m n, HVarVR0 v m)
         ss' = ss
               |> (HVarTL0 v m, HVarTL v m n)
               |> (HVarTR0 v m, HVarTR v m n)
     in (es', ss'))
  (mempty, mempty)

catMaybes' :: (Foldable t, Snoc (t a) (t a) a a, Monoid (t a))
           => t (Maybe a) -> t a
catMaybes' = foldl' (\acc -> maybe acc (acc |>)) mempty
