{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE StrictData        #-}

module Xenon.Types where

import           Control.Exception
import qualified Data.Sequence as SQ
import qualified Data.HashSet as HS
import qualified Data.Text as T
import           Data.DList

type Id  = T.Text
type Ids = HS.HashSet Id
type L   = SQ.Seq
type Output = DList String

data XenonExceptionType =
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

data XenonException =
  IE { exceptionSource  :: XenonExceptionType 
     , exceptionMessage :: String
     }

instance Show XenonException where
  show (IE src msg) = show src ++ ": " ++ msg

instance Exception XenonException
