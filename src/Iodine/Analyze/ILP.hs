{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Iodine.Analyze.ILP where

import           Control.Monad.LPMonad
import           Data.LinearProgram.Common
import           Data.LinearProgram as LP
import qualified Data.Map as M

objFun :: LinFunc String Int
objFun = linCombination [(10, "x1"), (6, "x2"), (4, "x3")]

(*&) :: (Ord v, Additive r) => r -> v -> LinFunc v r
n *& v = linCombination [(n,v)]

lp :: LPM String Int ()
lp = do
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

run :: IO ()
run = glpSolveVars mipDefaults (execLPM lp) >>= print