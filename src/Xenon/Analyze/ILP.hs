{-# LANGUAGE RecordWildCards #-}

module Xenon.Analyze.ILP (runILPLoop, runILP) where

import           Xenon.Types
import           Xenon.Utils (silence, getUserInput)

import           Control.Monad.LPMonad
import           Data.LinearProgram.Common
import           Data.LinearProgram as LP
import qualified Data.Map as M
import           Data.Graph.Inductive (Gr, nodes, pre)
import           Data.Foldable
import           Control.Monad
import           Data.Maybe
import           Data.List
import           Text.Printf

type ILPM = LPM String Integer

enableTrace :: Bool
enableTrace = False

-- | Either errorMessage (cannotMark, pubNodes, markedNodes)
runILPLoop :: [Int]
           -> [Int]
           -> [[Int]]
           -> Gr a b
           -> (Int -> Integer)
           -> (Int -> Id)
           -> IO (Either String ([Int], [Int], [Int]))
runILPLoop mustBePublic cannotMark loops graph ilpCosts toName = do
  for_ loops $ \l -> when (null l) $ error "loop must not be empty"
  res <- runILP mustBePublic cannotMark loops graph ilpCosts
  case res of
    Left _ -> return res
    Right (_, _, ms) | null ms -> return (Left "nothing to mark")
    Right (_, _, ms) -> do
      let ms' = (\m -> (toName m, m)) <$> ms
          sep = putStrLn $ replicate 80 '-'
      sep >> putStrLn "try marking these variables:" >> sep
      for_ ms' (printf "- %s\n" . fst)
      putStrLn ""
      putStrLn "Enter 'cannotMark' variable (empty to end the interaction):"
      mUserInput <- getUserInput
      case mUserInput of
        Nothing -> return res
        Just userInput -> do
          let mv = lookup userInput ms'
          let cannotMark'= maybe cannotMark (:cannotMark) mv
          runILPLoop mustBePublic cannotMark' loops graph ilpCosts toName

runILP :: [Int]
       -> [Int]
       -> [[Int]]
       -> Gr a b
       -> (Int -> Integer)
       -> IO (Either String ([Int], [Int], [Int]))
runILP mustBePublic _ _ _ _ | null mustBePublic =
  return (Left "must be public is empty")
runILP _ _ _ graph _ | null (nodes graph) =
  return (Left "graph is empty")
runILP mustBePublic cannotMark loops graph ilpCosts = do
  let lp = execLPM lpm
  when enableTrace $ do
    print mustBePublic
    print cannotMark
    print loops
    printLP lp
  let slnc = if enableTrace then id else silence
  (rc, msol) <- slnc $ glpSolveVars mipDefaults lp
  -- unless (rc == Success) $ do
  --   putStrLn "!!!!!!!!!!!!!!!!!!!!!!!!!"
  --   putStrLn "!!! ILP SOLVER FAILED !!!"
  --   putStrLn "!!!!!!!!!!!!!!!!!!!!!!!!!"
  return $
    if rc /= Success
      then Left $ "Solver returned " <> show rc
      else let (_cost, sol) = fromJust msol
               ns = nodes graph
               publicNodes = [n | n <- ns, let v = sol M.! pubNode n, v > 0.1]
               markedNodes = [n | n <- ns, let v = sol M.! markNode n, v > 0.1]
           in Right (cannotMark, publicNodes, markedNodes)
  where
    -- mustBePublic = mustBePublic0 \\ cannotMark

    pubNode n  = "pub_" <> show n
    markNode n = "mark_" <> show n

    lpm :: ILPM ()
    lpm = do
      setDirection Min
      setObjective objFun
      flowConstraints
      goalConstraints
      cannotMarkConstraints
      loopConstraints
      boundaryConstraints
      varKindConstraints

    objFun :: LinFunc String Integer
    objFun =
      add $ (\n -> ilpCosts n *& (markNode n)) <$> nodes graph

    flowConstraints =
      for_ (nodes graph) $ \n -> do
        let pn = pubNode n
            mn = markNode n
        let ps = pre graph n \\ [n]
        let m = if null ps then 1 else fromIntegral $ length ps
        let lhs = linCombination [(- m, pn), (m, mn)]
        let lhs' = if null ps
                   then lhs
                   else lhs LP.+ add [1 *& pubNode p | p <- ps]
        geqTo lhs' 0

    goalConstraints =
      for_ mustBePublic $ \n -> varEq (pubNode n) 1

    cannotMarkConstraints =
      for_ cannotMark $ \n -> varEq (markNode n) 0

    boundaryConstraints =
      for_ (nodes graph) $ \n -> do
        varBds (pubNode n) 0 1
        varBds (markNode n) 0 1

    loopConstraints =
      for_ loops $ \l -> do
        let s = fromIntegral $ length l
            lhs = add [(s *& markNode n) LP.- (1 *& pubNode n) | n <- l]
        geqTo lhs 0

    varKindConstraints =
      for_ (nodes graph) $ \n -> do
        setVarKind (pubNode n)  IntVar
        setVarKind (markNode n) IntVar

printLP :: (Show v, Show c, Ord c, Num c, Group c)
        => LP v c -> IO ()
printLP LP{..} = do
  print direction
  putStr "objective: "
  print objective
  for_ constraints print
  putStr "variable bounds: "
  print varBounds
  putStr "variable types: "
  print varTypes

(*&) :: (Ord v, Additive r) => r -> v -> LinFunc v r
n *& v = linCombination [(n,v)]

_test_run :: IO ()
_test_run = glpSolveVars mipDefaults (execLPM lp) >>= print
  where
    lp :: ILPM ()
    lp = do
      let objFun = linCombination [(10, "x1"), (6, "x2"), (4, "x3")]
      setDirection Max
      setObjective objFun
      leqTo (add $ map (1 *&) ["x1", "x2", "x3"]) 100
      leqTo (10 *& "x1" LP.+ 4 *& "x2" LP.+ 5 *& "x3") 600
      leqTo (linCombination [(2, "x1"), (2, "x2"), (6, "x3")]) 300
      varGeq "x1" 0
      varBds "x2" 0 50
      varGeq "x3" 0
      setVarKind "x1" IntVar
      setVarKind "x2" ContVar