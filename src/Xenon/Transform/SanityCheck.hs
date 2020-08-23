{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

module Xenon.Transform.SanityCheck (sanityCheck) where

import           Xenon.Language.Annotation
import           Xenon.Language.IR
import           Xenon.Types
import           Xenon.Utils

import           Control.Algebra
import           Control.Carrier.Reader
import           Control.Carrier.State.Strict
import           Control.Effect.Error
import           Control.Effect.Writer
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.List
-- import           Data.Maybe
import qualified Data.Sequence as SQ
import qualified Data.Text as T
import           Text.Printf
import Data.Maybe (isJust)

type A  = Int
type S  = Stmt A
type M  = Module A
type MI = ModuleInstance A
type MA = Maybe (AlwaysBlock A)

type K1 = (Id, Id)
type S1 = HS.HashSet K1
type ModuleMap = HM.HashMap Id M

type SC sig m = ( Has (Error XenonException) sig m    -- sanity error
                , Has (Reader (L M)) sig m             -- parsed IR
                , Has (Reader AnnotationFile) sig m    -- parsed annotation file
                , Has (Writer Output) sig m            -- output to stderr
                , Has (Reader ModuleMap) sig m
                -- , Effect sig
                )

type FD sig m = ( SC sig m
                , Has (Reader M) sig m
                , Has (Reader MA) sig m
                )

-- | Type alias for the Sanity Check Monad
type SCMI sig m = (SC sig m , Has (Reader M) sig m)

-- -----------------------------------------------------------------------------
sanityCheck :: SC sig m => m ()
-- -----------------------------------------------------------------------------
sanityCheck =
  sequence_ [ checkAssignmentsAreToLocalVariables
            , checkSameAssignmentType
            , checkUniqueUpdateLocationOfVariables
            , checkVariables
            ]

checkHelper :: (Has (Reader (L M)) sig m)
            => (S -> ReaderC MA (ReaderC M m) ())
            -> m ()
checkHelper goS = checkHelper' goS (\_ -> return ())

checkHelper' :: (Has (Reader (L M)) sig m)
             => (S -> ReaderC MA (ReaderC M m) ())
             -> (MI -> ReaderC M m ())
             -> m ()
checkHelper' goS goMI = ask @(L M) >>= traverse_ (checkModule goS goMI)

checkModule :: (Has (Reader (L M)) sig m)
            => (S -> ReaderC MA (ReaderC M m) ())
            -> (MI -> ReaderC M m ())
            -> M
            -> m ()
checkModule goS goMI m@Module{..} =
  ( do traverse_ goS gateStmts
         & runReader Nothing
       let goAB ab@AlwaysBlock{..} =
             goS abStmt & runReader (Just ab)
       traverse_ goAB alwaysBlocks
       traverse_ goMI moduleInstances
  ) & runReader m

getModuleName :: FD sig m => m Id
getModuleName = asks @M moduleName

-- -----------------------------------------------------------------------------
checkAssignmentsAreToLocalVariables :: SC sig m => m ()
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

handleAssignment :: Monad m
                 => (AssignmentType -> Expr a -> Expr a -> m ())
                 -> Stmt a
                 -> m ()
handleAssignment handler = go
  where
    gos = traverse_ go

    go Block{..}          = gos blockStmts
    go IfStmt{..}         = gos (ifStmtThen SQ.<| ifStmtElse SQ.<| SQ.empty)
    go Assignment{..}     = handler assignmentType assignmentLhs assignmentRhs
    go Skip{..}           = pure ()

-- -----------------------------------------------------------------------------
checkSameAssignmentType :: SC sig m => m ()
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
            blockStr = let maxLength = 400
                           str = prettyShow ab
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
checkUniqueUpdateLocationOfVariables :: SC sig m => m ()
-- -----------------------------------------------------------------------------

checkUniqueUpdateLocationOfVariables =
  checkHelper' (checkPrevious . asgnVars) handleModuleInstance
  & evalState (UniqueUpdateCheck HS.empty)

  where
    asgnVars :: Stmt a -> S1
    asgnVars Block{..}      = foldMap asgnVars blockStmts
    asgnVars IfStmt{..}     = asgnVars ifStmtThen <> asgnVars ifStmtElse
    asgnVars Assignment{..} = HS.singleton (varName assignmentLhs, varModuleName assignmentLhs)
    asgnVars Skip{..}       = mempty

handleModuleInstance :: (SCMI sig m, Has (State UniqueUpdateCheck) sig m)
                     => MI
                     -> m ()
handleModuleInstance mi@ModuleInstance{..} = do
  currentModuleName <- asks @M moduleName
  targetModule <- asks (HM.! moduleInstanceType)
  checkMIArguments targetModule mi
  targetModuleClocks <- getClocks moduleInstanceType
  let mPorts  = toHSet $ variableName . portVariable <$> ports targetModule
      miPorts = HM.keysSet moduleInstancePorts
  when (mPorts /= miPorts) $
    throw $ printf "Module instance is missing or have extra ports:\n%s" (prettyShow mi)
  let (_, miWrites) = moduleInstanceReadsAndWrites targetModule targetModuleClocks mi
  checkPrevious $ HS.map (, currentModuleName) miWrites

checkMIArguments :: SC sig m => M -> MI -> m ()
checkMIArguments m mi@ModuleInstance{..} =
  when (inputVars `intersects` outputVars) $
  throw $ printf "Module instance has overlapping variables in between input and output ports:\n%s" (prettyShow mi)
  where
    (inputVars, outputVars) =
      HM.foldlWithKey'
      (\acc p e ->
         acc & (if isOutput p then _2 else _1) <>~ getVariables e
      ) mempty moduleInstancePorts
    isOutput = (`elem` outputs)
    outputs  = moduleOutputs m mempty

newtype UniqueUpdateCheck = UniqueUpdateCheck { getUUCState :: S1 }

checkPrevious :: ( Has (State UniqueUpdateCheck) sig m
                 , Has (Error XenonException) sig m
                 )
              => S1 -> m ()
checkPrevious assignments = do
  oldAssignments <- gets getUUCState
  let newAssignments = oldAssignments `HS.union` assignments
  put (UniqueUpdateCheck newAssignments)
  when (HS.size oldAssignments + HS.size assignments /= HS.size newAssignments) $
    throw $ printf "found multiple assignments to variables from %s" (show $ toList assignments)


-- -----------------------------------------------------------------------------
checkVariables :: SC sig m => m ()
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
            ieVars =
              (af ^. initialEquals) <>
              foldMap (^. instanceEqualsVariables) (af ^. instanceInitialEquals)
            aeVars =
              (af ^. alwaysEquals) <>
              foldMap (^. instanceEqualsVariables) (af ^. instanceAlwaysEquals)
            isReg v = isJust $ Register v `SQ.elemIndexL` variables

        -- all annotation variables actually exist
        forM_ [ srcs
              , snks
              , ieVars
              , aeVars
              , af ^. assertEquals
              ] $ \vs ->
          unless (areVars vs) $
          throw $ printf "element(s) in %s is not a valid variable" (show vs)

        forM_ ieVars $ \v ->
          unless (isReg v) $
          throw $ printf "initial equal variable must be a register : %s" v

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

        -- -- sinks have to be registers
        -- for_ snks $ \snk ->
        --   when (isNothing $ Register snk `SQ.elemIndexL` variables) $
        --   throw $ printf "Sink %s is not found or not a register" snk

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
          output [ sep
                 , "non-input always_eq variables are given:"
                 , intercalate ", " $ T.unpack <$> toList nonInputAEs
                 , sep
                 ]
    )
  where
    s1 `subset` s2 = HS.null (HS.difference s1 s2)

throw :: Has (Error XenonException) sig m => String -> m a
throw = throwError . IE SanityCheck

emptyStmtData :: A
emptyStmtData = 0
