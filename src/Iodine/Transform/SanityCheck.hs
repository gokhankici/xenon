{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

module Iodine.Transform.SanityCheck (sanityCheck) where

import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.List
import           Data.Maybe
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Polysemy
import qualified Polysemy.Error as PE
import qualified Polysemy.Output as PO
import           Polysemy.Reader
import           Polysemy.State
import           Text.Printf

type A  = Int
type S  = Stmt A
type M  = Module A
type MI = ModuleInstance A
type MA = Maybe (AlwaysBlock A)

type K1 = (Id, Id)
type S1 = HS.HashSet K1
type ModuleMap = HM.HashMap Id M

data UniqueUpdateCheck m a where
  CheckPrevious :: S1 -> UniqueUpdateCheck m ()

makeSem ''UniqueUpdateCheck

type SC r = Members '[ PE.Error IodineException   -- sanity error
                     , Reader (L M)               -- parsed IR
                     , Reader AnnotationFile      -- parsed annotation file
                     , PO.Output String           -- output to stderr
                     , Reader ModuleMap
                     ] r

type FD r = ( SC r
            , Members '[ Reader M
                       , Reader MA
                       ] r
            )

-- | Type alias for the Sanity Check Monad
type SCM r a  = SC r => Sem (Reader MA ': Reader M ': r) a
type SCMI r a = SC r => Sem (Reader M ': r) a

-- -----------------------------------------------------------------------------
sanityCheck :: SC r => Sem r ()
-- -----------------------------------------------------------------------------
sanityCheck =
  sequence_ [ checkAssignmentsAreToLocalVariables
            , checkSameAssignmentType
            , checkUniqueUpdateLocationOfVariables
            , checkVariables
            ]

checkHelper :: SC r
            => (S -> SCM r ()) -- ^ checks the statement
            -> Sem r ()
checkHelper goS = checkHelper' goS (\_ -> return ())

checkHelper' :: SC r
             => (S -> SCM r ())  -- ^ checks the statement
             -> (MI-> SCMI r ()) -- ^ checks the module instance
             -> Sem r ()
checkHelper' goS goMI = ask @(L M) >>= traverse_ (checkModule goS goMI)

checkModule :: SC r
            => (S -> SCM r ())
            -> (MI -> SCMI r ())
            -> M
            -> Sem r ()
checkModule goS goMI m@Module{..} =
  ( do traverse_ goS gateStmts
         & runReader @MA Nothing
       let goAB ab@AlwaysBlock{..} =
             goS abStmt & runReader (Just ab)
       traverse_ goAB alwaysBlocks
       traverse_ goMI moduleInstances
  ) & runReader m

getModuleName :: FD r => Sem r Id
getModuleName = asks moduleName

-- -----------------------------------------------------------------------------
checkAssignmentsAreToLocalVariables :: SC r => Sem r ()
-- Check that all assignments in a single module are to the variables
-- of that module
-- -----------------------------------------------------------------------------
checkAssignmentsAreToLocalVariables =
  checkHelper $ handleAssignment $
  \assignmentType assignmentLhs assignmentRhs -> do
    moduleName <- getModuleName
    when (varModuleName assignmentLhs /= moduleName) $
      let stmt = Assignment{ stmtData = emptyStmtData, .. }
      in throw $ printf "%s :: lhs is not from the module %s" (show stmt) moduleName

handleAssignment :: (AssignmentType -> Expr a -> Expr a -> Sem r ())
                 -> Stmt a
                 -> Sem r ()
handleAssignment handler = go
  where
    gos = traverse_ go

    go Block{..}          = gos blockStmts
    go IfStmt{..}         = gos (ifStmtThen SQ.<| ifStmtElse SQ.<| SQ.empty)
    go Assignment{..}     = handler assignmentType assignmentLhs assignmentRhs
    go Skip{..}           = pure ()

-- -----------------------------------------------------------------------------
checkSameAssignmentType :: SC r => Sem r ()
-- check that always blocks with * events only have blocking assignments, and
-- the ones with @posedge or @negedge has non-blocking assignments
-- -----------------------------------------------------------------------------
checkSameAssignmentType =
  checkHelper $ handleAssignment $
  \assignmentType assignmentLhs assignmentRhs -> do
    let stmt = Assignment{stmtData = emptyStmtData, ..}
    mAB <- ask @MA
    case mAB of
      Nothing ->
        when (assignmentType /= Continuous) $
        throw $ printf "%s :: Assignments outside always blocks should be continous" (show stmt)
      Just ab@AlwaysBlock{..} ->
        let err  = throw $ printf
                   "%s does not match the event in %s" (show stmt) blockStr
            err2 = throw $ printf
                   "continuous assignment should not appear in an always block %s" blockStr
            blockStr = let maxLength = 200
                           str = show ab
                       in if length str > maxLength
                          then take maxLength str ++ " ..."
                          else str
        in case (abEvent, assignmentType) of
             (_, Continuous)         -> err2
             (Star, NonBlocking)     -> err
             (PosEdge{..}, Blocking) -> err
             (NegEdge{..}, Blocking) -> err
             _                       -> pure ()

-- -----------------------------------------------------------------------------
checkUniqueUpdateLocationOfVariables :: SC r => Sem r ()
-- -----------------------------------------------------------------------------
checkUniqueUpdateLocationOfVariables =
  checkHelper' (checkPrevious . asgnVars) handleModuleInstance
  & runUniqueUpdateCheck
  & evalState HS.empty

  where
    asgnVars :: Stmt a -> S1
    asgnVars Block{..}      = foldMap asgnVars blockStmts
    asgnVars IfStmt{..}     = asgnVars ifStmtThen <> asgnVars ifStmtElse
    asgnVars Assignment{..} = HS.singleton (varName assignmentLhs, varModuleName assignmentLhs)
    asgnVars Skip{..}       = mempty

handleModuleInstance :: SC r
                     => MI
                     -> Sem (Reader M ': UniqueUpdateCheck ': r) ()
handleModuleInstance mi@ModuleInstance{..} = do
  currentModuleName <- asks moduleName
  targetModule <- asks (HM.! moduleInstanceType)
  checkMIArguments targetModule mi
  targetModuleClocks <- getClocks moduleInstanceType
  let mPorts  = toHSet $ variableName . portVariable <$> ports targetModule
      miPorts = HM.keysSet moduleInstancePorts
  when (mPorts /= miPorts) $
    throw $ printf "Module instance is missing or have extra ports:\n%s" (prettyShow mi)
  let (_, miWrites) = moduleInstanceReadsAndWrites targetModule targetModuleClocks mi
  checkPrevious $ HS.map (, currentModuleName) miWrites

checkMIArguments :: SC r => M -> MI -> Sem r ()
checkMIArguments m mi@ModuleInstance{..} =
  unless (HS.null $ inputVars `HS.intersection` outputVars) $
  throw $ printf "Module instance has overlapping variables in between input and output ports:\n%s" (prettyShow mi)
  where
    (inputVars, outputVars) =
      HM.foldlWithKey'
      (\acc p e ->
         acc & (if isOutput p then _2 else _1) <>~ getVariables e
      ) mempty moduleInstancePorts
    isOutput = (`elem` outputs)
    outputs  = moduleOutputs m mempty

runUniqueUpdateCheck :: SC r => Sem (UniqueUpdateCheck ': r) a -> Sem (State S1 ': r) a
runUniqueUpdateCheck = reinterpret $ \case
  CheckPrevious assignments -> do
    oldAssignments <- get @S1
    modify (HS.union assignments)
    newAssignments <- get @S1
    when (HS.size oldAssignments + HS.size assignments /= HS.size newAssignments) $
      throw $ printf "found multiple assignments to variables from %s" (show $ toList assignments)

-- -----------------------------------------------------------------------------
checkVariables :: SC r => Sem r ()
-- -----------------------------------------------------------------------------
checkVariables =
  ask @(L M) >>= traverse_
    (\Module{..} -> do
        af <- getAnnotations moduleName
        let srcs = af ^. sources
            snks = af ^. sinks
            vars = foldr' HS.insert HS.empty (variableName <$> variables)
            (inputs, outputs) =
              foldl'
              (\(is, os) -> \case
                  Input p  -> (HS.insert (variableName p) is, os)
                  Output p -> (is, HS.insert (variableName p) os))
              (mempty, mempty)
              ports
            areVars vs = vs `subset` vars
            isInputVar v = v `HS.member` inputs
            isOutputVar v = v `HS.member` outputs

        -- all annotation variables actually exist
        forM_ [ srcs
              , snks
              , af ^. initialEquals
              , af ^. alwaysEquals
              , af ^. assertEquals
              ] $ \vs ->
          unless (areVars vs) $
          throw $ printf "element(s) in %s is not a valid variable" (show vs)

        clks  <- getClocks moduleName
        let isNotClock name = name `notElem` clks

        isTopModule <- (== moduleName) <$> asks (^. afTopModule)

        -- all inputs must be a source
        for_ ports $ \case
          Input v ->
            let name = variableName v
            in when (isTopModule && isNotClock name && not (HS.member name srcs)) $
               throw $ printf "The input port %s is not declared as a taint source!" name
          Output _ -> return ()

        -- sinks have to be registers
        for_ snks $ \snk ->
          when (isNothing $ Register snk `SQ.elemIndexL` variables) $
          throw $ printf "Sink %s is not found or not a register" snk

        -- always block events only refer to specified clocks
        for_ alwaysBlocks $ \AlwaysBlock{..} ->
          case abEvent of
            Star -> return ()
            _    ->
              let errMsg = T.unpack moduleName ++ ":: always block has bad event: " ++ show abEvent
              in case eventExpr abEvent of
                   Variable{..} ->
                     unless (varName `elem` clks && varModuleName == moduleName) $
                     throw errMsg
                   _ -> throw errMsg

        when (any isOutputVar (af ^. alwaysEquals)) $
          throw "an output port cannot be always_eq"

        when (any isInputVar (af ^. assertEquals)) $
          throw "an input port cannot be assert_eq"

        let nonInputAEs = (af ^. alwaysEquals) `HS.difference` inputs
        unless (HS.null nonInputAEs) $ do
          let sep = replicate 80 '#'
          PO.output sep
          PO.output "non-input always_eq variables are given:"
          PO.output (intercalate ", " $ T.unpack <$> toList nonInputAEs)
          PO.output sep

    )
  where
    s1 `subset` s2 = HS.null (HS.difference s1 s2)

throw :: Member (PE.Error IodineException) r => String -> Sem r a
throw = PE.throw . IE SanityCheck

emptyStmtData :: A
emptyStmtData = 0
