{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Iodine.Transform.Inline (inlineInstances, inlinePrefix) where

import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Lens
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Data.Bifunctor
import           Data.Foldable
import           Data.Traversable
import           Data.Maybe
-- import qualified Debug.Trace as DT

type A  = Int
type M  = Module A
type MI = ModuleInstance A
type ModuleMap = HM.HashMap Id M

-- modules should be in the topological order
inlineInstances :: (AnnotationFile, L M) -> (AnnotationFile, L M)
inlineInstances (af, ms) = (af', ms')
  where
    mm :: ModuleMap
    mm = foldl' (\acc m -> HM.insert (moduleName m) m acc) mempty ms

    maxCtr =
      let go m = maximum $
                 getData m <|
                 (getData <$> alwaysBlocks m) <>
                 (getData <$> moduleInstances m)
      in maximum (go <$> ms)

    (mm', af') =
      second (over afAnnotations (HM.filterWithKey (\mn _ -> canKeepModule mn))) $
      run $
      runState mm $ execState af $
      execState (ABCounter (maxCtr + 1)) $
      forM_ ms $ \m -> do
        m' <- inlineInstancesM m
        modify (HM.insert (moduleName m') m')

    toNewM m = mm' HM.! moduleName m
    ms' = toNewM <$> SQ.filter (canKeepModule . moduleName) ms

    -- canKeepModule mn = mn == af ^. afTopModule
    canKeepModule mn = fromMaybe True $ do
      ma <- af ^. (afAnnotations . at mn)
      return $ not $ ma ^. canInline

newtype ABCounter = ABCounter { getABCounter :: Int }

inlineInstancesM :: ( Has (State AnnotationFile) sig m
                    , Has (State ModuleMap) sig m
                    , Has (State ABCounter) sig m
                    )
                 => M -> m M
inlineInstancesM Module{..} = do
  (remainingInstances, newData) <-
    foldlM' (SQ.empty, SQ.empty) moduleInstances $ \(mis, nds) mi -> do
      -- let check = True
      check <- gets (^. afAnnotations
                      . to (HM.lookupDefault emptyModuleAnnotations (moduleInstanceType mi))
                      . canInline)
      if check
        then do let miType = moduleInstanceType mi
                    miName = moduleInstanceName mi
                miClocks <- getMIClocks mi
                let clkMap v = if v `elem` miClocks
                               then case HM.lookup v (moduleInstancePorts mi) of
                                      Just Variable{..} -> Just varName
                                      _ -> Nothing
                               else Nothing
                    rst = InlineSt moduleName miType miName (getData mi) clkMap
                nd <- inlineInstance mi & runReader rst
                return (mis, nds |> nd)
        else return (mis |> mi, nds)
  return $ Module { variables       = variables          <> foldMap (^._1) newData
                  , constantInits   = constantInits      <> foldMap (^._2) newData
                  , gateStmts       = gateStmts          <> foldMap (^._3) newData
                  , alwaysBlocks    = alwaysBlocks       <> foldMap (^._4) newData
                  , moduleInstances = remainingInstances <> foldMap (^._5) newData
                  , ..
                  }

type NewData = ( L Variable
               , L (Id, Expr A)
               , L (Stmt A)
               , L (AlwaysBlock A)
               , L MI
               )

data InlineSt = InlineSt { getCurrentModuleName :: Id
                         , getMIType            :: Id
                         , getMIName            :: Id
                         , getMIId              :: Int
                         , getClockMapping      :: Id -> Maybe Id
                         }

inlineInstance :: ( Has (State AnnotationFile) sig m
                  , Has (State ModuleMap) sig m
                  , Has (Reader InlineSt) sig m
                  , Has (State ABCounter) sig m
                  )
               => MI -> m NewData
inlineInstance mi@ModuleInstance{..} = do
  inlineSt <- ask
  m@Module{..} :: M <- gets (HM.! moduleInstanceType)
  vs  <- traverse fixVariable variables
  cis <- traverse (\(v,e) -> (,) <$> fixName v <*> return e) constantInits
  gs  <- traverse fixStmt gateStmts
  as  <- traverse fixAB alwaysBlocks
  mis <- traverse fixMI moduleInstances
  clks <- getMIClocks mi
  let miInputs = moduleInputs m clks
      miOutputs = moduleOutputs m mempty
      mkPortVar p = Variable
                    <$> fixName p
                    <*> return (getCurrentModuleName inlineSt)
                    <*> return pureA
  extraGS <- for (toSequence miInputs) $ \i -> do
    let e = moduleInstancePorts HM.! i
    lhs <- mkPortVar i
    return $ Assignment Continuous lhs e pureA
  miOutputAssigns <- for (toSequence miOutputs) $ \o -> do
    let e = moduleInstancePorts HM.! o
    rhs <- mkPortVar o
    return $ Assignment Blocking e rhs pureA
  extraABs <- forM miOutputAssigns (\s -> AlwaysBlock Star s <$> freshABIndex)

  -- update the initial & always equal annotations of the current module
  miMA <- gets (^. afAnnotations
                 . to (HM.lookupDefault emptyModuleAnnotations moduleInstanceType))
  let computeNewAnnots l = HS.fromList <$> traverse fixName (miMA ^. moduleAnnotations . l . to toList)
  extraIEs1 <- computeNewAnnots initialEquals
  extraAEs1 <- computeNewAnnots alwaysEquals
  let ma = miMA ^. moduleAnnotations
      instanceEqualsUpdate l =
        let ies = ma ^. l in
        (flip mfoldM) ies $ \ie ->
          if ie ^. instanceEqualsParentModule == getCurrentModuleName inlineSt &&
             ie ^. instanceEqualsInstanceName == moduleInstanceName
          then HS.fromList <$> traverse fixName (toList $ ie ^. instanceEqualsVariables)
          else return mempty
  extraIEs2 <- instanceEqualsUpdate instanceInitialEquals
  extraAEs2 <- instanceEqualsUpdate instanceAlwaysEquals
  let extraIEs = extraIEs1 <> extraIEs2
      extraAEs = extraAEs1 <> extraAEs2
  newQualifiers <- traverse fixQualifier (miMA ^. moduleQualifiers)
  let updateA = over initialEquals (<> extraIEs) . over alwaysEquals (<> extraAEs)
      updateMA = Just .
                 over moduleQualifiers (<> newQualifiers) .
                 over moduleAnnotations updateA .
                 fromMaybe emptyModuleAnnotations
  cmn <- asks getCurrentModuleName
  modify $ over afAnnotations $ HM.alter updateMA cmn

  return (vs, cis, gs <> extraGS, as <> extraABs, mis)

freshABIndex :: Has (State ABCounter) sig m => m Int
freshABIndex = do
  n <- gets getABCounter
  put (ABCounter (n+1))
  return n

fixVariable :: Has (Reader InlineSt) sig m => Variable -> m Variable
fixVariable = \case
  Wire w     -> Wire     <$> fixName w
  Register r -> Register <$> fixName r

inlinePrefix :: Id
inlinePrefix = "IodInl_M_"

fixName :: Has (Reader InlineSt) sig m => Id -> m Id
fixName v = do
  miType <- asks getMIType
  miName <- asks getMIName
  miId <- asks getMIId
  return $
    inlinePrefix <> miType
    <> "_I_" <> miName
    <> "_V_" <> v
    <> "_T" <> T.pack (show miId)

fixExpr :: Has (Reader InlineSt) sig m => Expr a -> m (Expr a)
fixExpr e@Constant{} = return e
fixExpr e@Str{}      = return e
fixExpr Variable{..} = Variable
                       <$> fixName varName
                       <*> asks getCurrentModuleName
                       <*> return exprData
fixExpr UF{..}       = UF ufOp <$> traverse fixExpr ufArgs <*> return exprData
fixExpr IfExpr{..}   = IfExpr
                       <$> fixExpr ifExprCondition
                       <*> fixExpr ifExprThen
                       <*> fixExpr ifExprElse
                       <*> return exprData
fixExpr Select{..}   = Select
                       <$> fixExpr selectVar
                       <*> traverse fixExpr selectIndices
                       <*> return exprData
fixExpr VFCall{..}   = notSupported

fixStmt :: Has (Reader InlineSt) sig m => Stmt a -> m (Stmt a)
fixStmt Block{..}      = Block <$> traverse fixStmt blockStmts <*> return stmtData
fixStmt Assignment{..} = Assignment assignmentType
                         <$> fixExpr assignmentLhs
                         <*> fixExpr assignmentRhs
                         <*> return stmtData
fixStmt IfStmt{..}     = IfStmt
                         <$> fixExpr ifStmtCondition
                         <*> fixStmt ifStmtThen
                         <*> fixStmt ifStmtElse
                         <*> return stmtData
fixStmt s@Skip{}       = return s

fixAB :: Has (Reader InlineSt) sig m => AlwaysBlock a -> m (AlwaysBlock a)
fixAB AlwaysBlock{..} = AlwaysBlock <$> fixEvent abEvent <*> fixStmt abStmt <*> return abData
  where
    fixEvent Star        = return Star
    fixEvent (PosEdge e) = PosEdge <$> fixEventExpr e
    fixEvent (NegEdge e) = NegEdge <$> fixEventExpr e

    fixEventExpr e@Variable{..} =
      do mc <- ($ varName) <$> asks getClockMapping
         case mc of
           Just v -> Variable v <$> asks getCurrentModuleName <*> return exprData
           Nothing -> fixExpr e
    fixEventExpr e = fixExpr e

fixMI :: Has (Reader InlineSt) sig m => ModuleInstance a -> m (ModuleInstance a)
fixMI ModuleInstance{..} = ModuleInstance moduleInstanceType moduleInstanceName
                           <$> traverse fixExpr moduleInstancePorts
                           <*> return moduleInstanceData

fixQualifier :: Has (Reader InlineSt) sig m => Qualifier -> m Qualifier
fixQualifier = \case
  QImplies v vs -> QImplies <$> fixName v <*> traverse fixName vs
  QIff     v vs -> QIff <$> fixName v <*> traverse fixName vs
  QPairs   vs   -> QPairs <$> traverse fixName vs

pureA :: A
pureA = 0

getMIClocks :: Has (State AnnotationFile) sig m => ModuleInstance Int -> m Ids
getMIClocks ModuleInstance{..} =
  gets (^. afAnnotations . to (HM.lookupDefault emptyModuleAnnotations moduleInstanceType) . clocks)
