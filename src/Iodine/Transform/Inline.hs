{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Iodine.Transform.Inline (inlineInstances) where

import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Carrier.Reader
import           Control.Lens
import qualified Data.HashMap.Strict as HM
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Data.Traversable

type A  = Int
type M  = Module A
type MI = ModuleInstance A
type ModuleMap = HM.HashMap Id M

inlineInstances :: ( Has (Reader AnnotationFile) sig m
                   , Has (Reader ModuleMap) sig m
                   , Traversable t
                   )
                => t M -- ^ 'traverse' should visit these modules in topological order
                -> m (t M)
inlineInstances = traverse inlineInstancesM

inlineInstancesM :: ( Has (Reader AnnotationFile) sig m
                    , Has (Reader ModuleMap) sig m
                    )
                 => M -> m M
inlineInstancesM m@Module{..} = do
  (remainingInstances, newData) <-
    foldlM' (SQ.empty, SQ.empty) moduleInstances $ \(mis, nds) mi -> do
    -- check <- view canInline <$> getModuleAnnotations (moduleInstanceType mi)
    let check = True
    if check
      then do let miType = moduleInstanceType mi
              miClocks <- getClocks miType
              let clkMap v = if v `elem` miClocks
                             then case HM.lookup v (moduleInstancePorts mi) of
                                    Just Variable{..} -> Just varName
                                    _ -> Nothing
                             else Nothing
                  rst = InlineSt moduleName variables miType (getData mi) clkMap
              nd <- inlineInstance mi & runReader rst
              return (mis, nds |> nd)
      else return (mis |> mi, nds)
  return $ Module { variables       = variables     <> foldMap (^._1) newData
                  , constantInits   = constantInits <> foldMap (^._2) newData
                  , gateStmts       = gateStmts     <> foldMap (^._3) newData
                  , alwaysBlocks    = alwaysBlocks  <> foldMap (^._4) newData
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
                         , getCurrentModuleVars :: L Variable
                         , getMIType            :: Id
                         , getMIName            :: Int
                         , getClockMapping      :: Id -> Maybe Id
                         }

inlineInstance :: ( Has (Reader AnnotationFile) sig m
                  , Has (Reader ModuleMap) sig m
                  , Has (Reader InlineSt) sig m
                  )
               => MI -> m NewData
inlineInstance mi@ModuleInstance{..} = do
  m@Module{..} :: M <- asks (HM.! moduleInstanceType)
  vs  <- traverse fixVariable variables
  cis <- traverse (\(v,e) -> (,) <$> fixName v <*> return e) constantInits
  gs  <- traverse fixStmt gateStmts
  as  <- traverse fixAB alwaysBlocks
  mis <- traverse fixMI moduleInstances
  let miInputs = moduleInputs m mempty
  extraGS <- for (toSequence miInputs) $ \i -> do
    let e = moduleInstancePorts HM.! i
    lhs <- Variable <$> fixName i <*> asks getCurrentModuleName <*> return pureA
    return $ Assignment Continuous lhs e pureA
  cmVars <- asks getCurrentModuleVars
  let isWire v = Wire v `elem` cmVars
  -- TODO add gate statements for the instantiation of the instance output ports
  return (vs, cis, gs <> extraGS, as, mis)

fixVariable :: Has (Reader InlineSt) sig m => Variable -> m Variable
fixVariable = \case
  Wire w     -> Wire     <$> fixName w
  Register r -> Register <$> fixName r

fixName :: Has (Reader InlineSt) sig m => Id -> m Id
fixName v = do
  miType <- asks getMIType
  miName <- asks getMIName
  return $ "M_" <> miType <> "_T" <> T.pack (show miName) <> "_" <> v

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

pureA :: A
pureA = 0
