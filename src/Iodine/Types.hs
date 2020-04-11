{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE StrictData        #-}

module Iodine.Types where

import           Control.Exception
import qualified Data.Sequence as SQ
import qualified Data.HashSet as HS
import qualified Data.Text as T
import           Data.DList

type Id  = T.Text
type Ids = HS.HashSet Id
type L   = SQ.Seq
type Output = DList String

data IodineExceptionType =
    IRParser
  | SanityCheck
  | Merge
  | Normalize
  | VCGen
  | Query
  | Assert
  | NotSupported
  | Analysis
  deriving (Show, Eq)

data IodineException =
  IE { exceptionSource  :: IodineExceptionType 
     , exceptionMessage :: String
     }

instance Show IodineException where
  show (IE src msg) = show src ++ ": " ++ msg

instance Exception IodineException
