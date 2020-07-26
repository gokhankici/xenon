{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}

module Iodine.Analyze.GuessQualifiers
  ( guessQualifiers
  )
where

import           Iodine.Analyze.ModuleSummary
import           Iodine.Analyze.DependencyGraph
import           Iodine.Language.Annotation
import           Iodine.Language.IR
import           Iodine.Types
import           Iodine.Utils

import qualified Data.Graph.Inductive          as G
import qualified Data.HashMap.Strict           as HM
import qualified Data.IntMap                   as IM
import qualified Data.IntSet                   as IS
import           Data.Foldable
import           Data.Maybe
import qualified Data.Sequence                 as SQ
import           Data.Bifunctor
-- import Data.List (nub)

import qualified Debug.Trace as DT

trc :: String -> a -> a
trc msg =
  let enableTrace = False
  in if enableTrace then DT.trace msg else id

data St =
  St { summary  :: ModuleSummary
     , worklist :: L Int
     , history  :: IS.IntSet
     , cycleMap :: IM.IntMap Int
     }
  deriving (Show)

guessQualifiers :: Module Int -> Ids -> ModuleSummary -> L Qualifier
guessQualifiers Module{..} srcs ms = res <> miQualifs
 where
  miQualifs = mkMIQualif <$> moduleInstances
  mkMIQualif mi = QPairs . toSequence $ mfold getVariables $ moduleInstancePorts mi

  res =
    ( \ns -> let vs = withLen "guessQualifiers: " $ SQ.filter filterVars (ns >>= sccToName)
             in  QPairs vs
    ) <$> sameCycles
  withLen s ls = trc (s <> show (length ls)) ls

  sameCycles = trc (show $ toList $ fmap toName <$> _sameCycles) _sameCycles
  _sameCycles =
    SQ.fromList
      $   filter checkSCCNode
      $   fmap (SQ.fromList . snd)
      $   groupSort
      $   swap
      <$> IM.toList (trc (show cycleMap) cycleMap)
  checkSCCNode = \case
    SQ.Empty           -> False
    sn SQ.:<| SQ.Empty -> (> 1) . IS.size . fromJust $ G.lab g sn
    _                  -> True
  St {..} = loop St { summary  = ms
                    , worklist = SQ.fromList $ G.topsort g
                    , history  = IS.fromList startSCCNodes
                    , cycleMap = IM.fromList $ (, 0) <$> startSCCNodes
                    }
  filterVars = (`notElem` temporaryVariables ms)
  _g  = variableDependenciesSCC ms
  msg = second (fmap (invVariableDependencyNodeMap ms IM.!) . IS.toList) <$> G.labNodes _g
  -- msg = nub $ IS.size . snd <$> G.labNodes _g
  g = trc (show msg) _g

  toName = (invVariableDependencyNodeMap ms IM.!)

  sccToName sn = fmap toName $ SQ.fromList $ IS.toList $ fromJust $ G.lab g sn
  startSCCNodes =
    (variableDependencySCCNodeMap ms IM.!)
      .   (variableDependencyNodeMap ms HM.!)
      <$> toList srcs

loop :: St -> St
loop St {..}
  | trc ("loop: " <> show (IM.toList cycleMap, worklist, IS.toList history))
        False
  = undefined
loop St {..} | n SQ.:<| ns <- worklist, IS.member n history =
  loop St { worklist = ns, .. }
loop St {..} | n SQ.:<| ns <- worklist =
  let g       = variableDependenciesSCC summary
      parents = G.lpre g n
      getCycleNo (p, t) =
          let c = fromMaybe (-1) $ IM.lookup p cycleMap
          in  case t of
                Implicit    -> c
                Explicit nb -> if nb then c + 1 else c
      cycleNo = if null parents then (-1) else maximum $ getCycleNo <$> parents
  in  loop St { worklist = ns <> SQ.fromList (G.suc g n)
              , cycleMap = IM.insert n cycleNo cycleMap
              , history  = IS.insert n history
              , ..
              }
loop st = st
