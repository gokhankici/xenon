{-# LANGUAGE RecordWildCards #-}

module Iodine.Analyze.ILP (runILPLoop, runILP) where

import           Iodine.Types
import           Control.Monad.LPMonad
import           Data.LinearProgram.Common
import           Data.LinearProgram as LP
import qualified Data.Map as M
import qualified Data.Graph.Inductive as G
import           Data.Foldable
import           Control.Monad
import           Data.Maybe
import           Data.List
import qualified Data.Text as T
import           System.IO

type ILPM = LPM String Int

enableTrace :: Bool
enableTrace = False

runILPLoop :: [Int]
           -> [Int]
           -> G.Gr a b
           -> (Int -> Id)
           -> IO (Either String ([Int], [Int]))
runILPLoop mustBePublic cannotMark graph toName = do
  res <- runILP mustBePublic cannotMark graph
  case res of
    Left _ -> return res
    Right (_, ms) | null ms -> return res
    Right (_, ms) -> do
      let ms' = (\m -> (toName m, m)) <$> ms
          sep = putStrLn $ replicate 80 '-'
      sep >> putStrLn "try marking these variables:" >> sep
      for_ ms' (putStrLn . T.unpack . fst)
      putStrLn ""
      putStrLn "Enter 'cannotMark' variable (empty to end the interaction):"
      mcmNode <-  (>>= (`lookup` ms')) <$> getUserInput
      case mcmNode of
        Nothing -> return res
        Just n -> runILPLoop mustBePublic (n:cannotMark) graph toName

getUserInput :: IO (Maybe Id)
getUserInput = do
  eof <- hIsEOF stdin
  if eof
    then return Nothing
    else do i <- T.strip . T.pack <$> hGetLine stdin
            return $ if T.null i then Nothing else Just i

runILP :: [Int]
       -> [Int]
       -> G.Gr a b
       -> IO (Either String ([Int], [Int]))
runILP mustBePublic0 cannotMark graph = do
  let lp = execLPM lpm
  when enableTrace $ printLP lp
  (rc, msol) <- glpSolveVars mipDefaults lp
  unless (rc == Success) $ do
    putStrLn "!!!!!!!!!!!!!!!!!!!!!!!!!"
    putStrLn "!!! ILP SOLVER FAILED !!!"
    putStrLn "!!!!!!!!!!!!!!!!!!!!!!!!!"
  return $
    if rc /= Success
      then Left $ "Solver returned " <> show rc
      else let (_cost, sol) = fromJust msol
               ns = G.nodes graph
               publicNodes = [n | n <- ns, let v = sol M.! pubNode n, v > 0.1]
               markedNodes = [n | n <- ns, let v = sol M.! markNode n, v > 0.1]
           in Right (publicNodes, markedNodes)
  where
    mustBePublic = mustBePublic0 \\ cannotMark
    pubNode n  = "pub_" <> show n
    markNode n = "mark_" <> show n

    lpm :: ILPM ()
    lpm = do
      setDirection Min
      setObjective objFun
      flowConstraints
      goalConstraints
      cannotMarkConstraints
      boundaryConstraints
      varKindConstraints

    objFun :: LinFunc String Int
    objFun = add $ (1 *&) . markNode <$> G.nodes graph

    flowConstraints, goalConstraints, cannotMarkConstraints, varKindConstraints, boundaryConstraints :: ILPM ()
    flowConstraints =
      for_ (G.nodes graph) $ \n -> do
        let pn = pubNode n
            mn = markNode n
        let ps = G.pre graph n
        let m = if null ps then 1 else length ps
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
      -- return ()
      for_ (G.nodes graph) $ \n -> do
        varBds (pubNode n) 0 1
        varBds (markNode n) 0 1

    varKindConstraints =
      for_ (G.nodes graph) $ \n -> do
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