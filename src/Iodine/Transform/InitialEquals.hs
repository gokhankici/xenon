{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}
module Iodine.Transform.InitialEquals (computeAllInitialEqualVars) where

import           Iodine.Analyze.DependencyGraph (VarDepEdgeType)
import           Iodine.Analyze.ModuleSummary
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Effect.Error
import qualified Control.Effect.Trace as CET
import           Control.Effect.Writer
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.Graph.Inductive as G
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Sequence as SQ
import           Data.Hashable (Hashable)
import           Text.Printf

type ModuleMap = HM.HashMap Id (Module Int)

newtype Var = Var { _getVar :: (Id, Id) }
              deriving (Eq, Hashable)

type Vars = HS.HashSet Var

mkVar :: Id -> Id -> Var
mkVar m v = Var (m, v)

getVarModule, getVarName :: Var -> Id
getVarModule (Var (m,_)) = m
getVarName (Var (_,v)) = v

data Reason = Reason
  { dependsOnInputs :: Vars
  , dependsOnReg    :: Vars
  -- , writtenByMI     :: HS.HashSet (Id, Id, Id) -- module name, module instance, output port
  , uninitialized   :: Vars
  }

type VarReasonMap = HM.HashMap Id (Maybe Reason) -- var -> reason

type ModuleReasonMap = HM.HashMap (Id, Ids) VarReasonMap -- (module, initial_eq vars) -> ...

data ReadSt = ReadSt
  { sccG      :: G.Gr IS.IntSet VarDepEdgeType
  , sccNodes  :: IM.IntMap Int
  , mInputs   :: Ids
  , mRegs     :: Ids
  , ms        :: ModuleSummary
  , m         :: Module Int
  }

type G sig m =
  ( Has (Reader AnnotationFile) sig m
  , Has (Error IodineException) sig m
  , Has CET.Trace sig m
  , Has (Reader ModuleMap) sig m
  , Has (Reader SummaryMap) sig m
  , Has (Writer Output) sig m
  )

type FDEQ sig m =
  ( G sig m
  , Has (State VarReasonMap) sig m
  , Has (Reader ReadSt) sig m
  , Has (Reader ModuleReasonMap) sig m -- past modules' reasons
  , Has (Reader CurrentIEs) sig m
  )

type GenericModuleReasonMap = HM.HashMap Id Ids

newtype CurrentIEs = CurrentIEs { getCurrentIEs :: Ids }

computeAllInitialEqualVars :: G sig m => L (Module Int) -> m GenericModuleReasonMap
computeAllInitialEqualVars modules =
  execState (mempty :: GenericModuleReasonMap) $
  evalState (mempty :: ModuleReasonMap) $
  getAllPossibleConfigurations modules
    >>= traverse_ handleModuleConfiguration

-- | compute the initial equals for the given configuration of the module
handleModuleConfiguration :: ( G sig m
                             , Has (State ModuleReasonMap) sig m
                             , Has (State GenericModuleReasonMap) sig m
                             )
                          => (Module Int, Ids, Bool)
                          -> m ()
handleModuleConfiguration (currentModule, currentIEs, isGeneric) = do
  reasonHistory <- get @ModuleReasonMap
  reasons <-
    autoInitialEqualVars currentModule
    & runReader reasonHistory
    & runReader (CurrentIEs currentIEs)
  modify @ModuleReasonMap (at (mn, currentIEs) ?~ reasons)

  when isGeneric $ do
    genericIEs <-
      execState (HS.empty :: Ids) $
      for_ (HM.toList reasons) $ \(v, mr) ->
      case mr of
        Nothing -> modify @Ids (HS.insert v)
        Just Reason{..} ->
          if | notNull dependsOnInputs ->
               CET.trace $ "not initial_eq : Depends on inputs "
               <> show (mn, v, toList dependsOnInputs)

             | notNull dependsOnReg ->
               CET.trace $ "not initial_eq : Depends on non-sanitized register "
               <> show (mn, v, toList dependsOnReg)

             | notNull uninitialized ->
               CET.trace $ "not initial_eq : Depends on uninitialized variables "
               <> show (mn, v, toList uninitialized)

             | otherwise -> error "unreachable"
    modify @GenericModuleReasonMap (at mn ?~ genericIEs)

  where
    notNull = not . HS.null
    mn = moduleName currentModule

-- | list of modules, the all possible initial equals, and whether it's the "generic" module
getAllPossibleConfigurations :: G sig m => L (Module Int) -> m (L (Module Int, Ids, Bool))
getAllPossibleConfigurations modules = do
  res <- forM modules $ \m@Module{..} -> do
    as <- getAnnotations moduleName
    let allInstanceInitialEquals =
          (as ^. instanceInitialEquals) <> (as ^. instanceAlwaysEquals)
        allMentionedInstances =
          HS.toList $
          foldl' (\acc ie ->
            let ci = ( ie ^. instanceEqualsParentModule
                     , ie ^. instanceEqualsInstanceName
                     )
            in HS.insert ci acc
          ) mempty allInstanceInitialEquals
    let getIEs = getModuleIEs moduleName
    iesG <- getIEs Nothing
    iesI <- SQ.fromList . nub' id . filter (/= iesG)
            <$> forM (Just <$> allMentionedInstances) getIEs
    return $ (m, iesG, True) <| fmap (m, , False) iesI
  return $ foldl' (<>) mempty res

-- Nothing    : general instance
-- Just (p,i) : specific instance in parent module p with name i
getModuleIEs :: G sig m => Id -> Maybe (Id, Id) -> m Ids
getModuleIEs currentModuleName mCurrentInstance = do
  as <- getAnnotations currentModuleName
  let usualInitialEquals =
        (as ^. initialEquals) <> (as ^. alwaysEquals)
      allInstanceInitialEquals =
        (as ^. instanceInitialEquals) <> (as ^. instanceAlwaysEquals)
      extraInits = case mCurrentInstance of
        Nothing -> mempty
        Just (pm, ins) ->
          foldl' (\acc ie ->
            if ie ^. instanceEqualsParentModule == pm &&
               ie ^. instanceEqualsInstanceName == ins
            then acc <> ie ^. instanceEqualsVariables
            else acc
          ) mempty allInstanceInitialEquals
  return (usualInitialEquals <> extraInits)

autoInitialEqualVars :: ( G sig m
                        , Has (Reader ModuleReasonMap) sig m
                        , Has (Reader CurrentIEs) sig m
                        )
                     => Module Int
                     -> m VarReasonMap
autoInitialEqualVars m@Module{..} = do
  ms@ModuleSummary{..} <- asks (hmGet 14 moduleName)
  moduleMap  <- ask
  summaryMap <- ask
  let fixedG = varDepGraphWithInstanceEdges m moduleMap summaryMap
      (sccG, toSCCNodeMap) = sccGraph fixedG
      readSt = ReadSt
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
  ReadSt{..} <- ask
  let thisSCC = G.context sccG sccNode ^. _3
  for_ (IS.toList thisSCC) autoInitialEqualVarsRunOriginalNode


autoInitialEqualVarsRunOriginalNode :: FDEQ sig m => Int -> m (Maybe Reason)
autoInitialEqualVarsRunOriginalNode n = do
  ModuleSummary{..} <- asks ms
  let toVar = (invVariableDependencyNodeMap IM.!)
      toNode = (variableDependencyNodeMap HM.!)
      nName = toVar n
  mSt <- gets (HM.lookup nName)
  case mSt of
    Just st -> return st
    Nothing -> do
      currentModuleName <- asks (moduleName . m)
      -- as <- getAnnotations currentModuleName
      ReadSt{..} <- ask
      ies <- asks getCurrentIEs
      let isIE     = nName `elem` ies
          isWire   = not . (`elem` mRegs)
          isIn     = nName `elem` mInputs
          nNameSet = HS.singleton $ mkVar currentModuleName nName
      st <-
        if
          -- variable is initial_eq
          | isIE -> return Nothing

          -- variable is an input
          | isIn -> return $ Just mempty {dependsOnInputs = nNameSet}

          | isWire nName -> case G.pre variableDependencies n of
            [] -> -- variable has no dependency?
              case HM.lookup nName threadWriteMap of
                -- if no one updates this variable, it must be uninitialized
                Nothing ->
                  return $ Just mempty {uninitialized = nNameSet }

                Just miId ->
                  case find ((== miId) . getData) (moduleInstances m) of
                    -- variable is initialized with constant value
                    Nothing -> return Nothing

                    -- variable is written by a module instance
                    Just ModuleInstance{..} -> do

                      let miPorts = HM.toList moduleInstancePorts
                          miInputLookup i  = snd $ find' ((== i) . fst) miPorts
                          miOutputLookup o = fst $ find' (eqVarName o . snd) miPorts
                          outputPort = miOutputLookup nName

                      -- current instance
                      let currentInstance = Just (currentModuleName, moduleInstanceName)
                      -- initial equalities of the current instance
                      instanceIEs <- getModuleIEs moduleInstanceType currentInstance
                      -- variable map of the configuration of the current instance
                      reasonVarMap <-
                        asks @ModuleReasonMap (HM.! (moduleInstanceType, instanceIEs))

                      case reasonVarMap HM.! outputPort of
                        -- output port itself is sanitized
                        Nothing -> return Nothing

                        -- there's a reason why output port is not sanitized,
                        -- and it depends on a module input
                        Just reason | not (HS.null (dependsOnInputs reason)) -> do
                          let errMsg = "reason: " <> show (currentModuleName, reason)

                          -- find the reason why the input(s) are not sanitized
                          resolvedReason <-
                            fmap mergeReasons $
                            forM (toList (dependsOnInputs reason)) $ \iv -> do
                              let ivm = getVarModule iv
                                  ivn = getVarName iv
                              unless (ivm == moduleInstanceType) $ do
                                output [errMsg]
                                error "dependsOnInputs module does not refer to the same module"
                              let inputExpr = miInputLookup ivn
                                  inputExprVars = toList $ getVariables inputExpr
                              mergeReasons <$> forM inputExprVars (autoInitialEqualVarsRunOriginalNode . toNode)

                          -- make sure that all current input dependencies refer
                          -- to the current module
                          let allInputsReferToCurrent r =
                                all ((== currentModuleName) . getVarModule) (dependsOnInputs r)
                              sanityCheck = maybe True allInputsReferToCurrent resolvedReason
                          unless sanityCheck $ do
                            output [errMsg, show resolvedReason]
                            error "all variables do not refer to the current module"

                          return resolvedReason

                        -- there's a reason why output port is not sanitized,
                        -- but it does not depend on a module input
                        reason -> return reason

            parents -> -- variable is updated by some other variables
              mergeReasons <$> traverse autoInitialEqualVarsRunOriginalNode parents

          -- variable is non-sanitized register
          | otherwise -> return $ Just mempty {dependsOnReg = nNameSet}
      modify @VarReasonMap (at nName ?~ st)
      return st
  where
    eqVarName str = \case
      Variable{..} -> varName == str
      _ -> False

mergeReasons :: Foldable t => t (Maybe Reason) -> Maybe Reason
mergeReasons = foldl' go Nothing
  where
    go Nothing b = b
    go a Nothing = a
    go (Just a) (Just b) = Just (a <> b)

instance Semigroup Reason where
  v1 <> v2 = Reason
    { dependsOnInputs = dependsOnInputs v1 <> dependsOnInputs v2
    , dependsOnReg    = dependsOnReg v1 <> dependsOnReg v2
    , uninitialized   = uninitialized v1 <> uninitialized v2
    }

instance Monoid Reason where
  mempty = Reason mempty mempty mempty

instance Show Reason where
  show Reason{..} =
    printf "(inputs: %s, regs: %s, init: %s)"
      (show $ toList dependsOnInputs)
      (show $ toList dependsOnReg)
      (show $ toList uninitialized)

instance Show Var where
  show (Var (m, v)) = show (m, v)
