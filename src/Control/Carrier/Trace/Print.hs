{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Carrier.Trace.Print
( runTrace
, runTraceIgnore
, TraceC(..)
, module Control.Effect.Trace
) where

import           Control.Algebra
import           Control.Applicative (Alternative(..))
import           Control.Effect.Trace
import           Control.Monad (MonadPlus(..))
import qualified Control.Monad.Fail as Fail
import           Control.Monad.Fix
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import           System.IO

-- | print to stdout instead of stderr like 'Control.Carrier.Trace.Printing'
runTrace :: TraceC m a -> m a
runTrace (TraceC m) = m

runTraceIgnore :: TraceC m a -> m a
runTraceIgnore (TraceC m) = m

newtype TraceC m a = TraceC (m a)
  deriving (Alternative, Applicative, Functor, Monad, Fail.MonadFail, MonadFix, MonadIO, MonadPlus)

instance MonadTrans TraceC where
  lift = TraceC
  {-# INLINE lift #-}

instance (MonadIO m, Algebra sig m) => Algebra (Trace :+: sig) (TraceC m) where
  alg (L (Trace s k)) = liftIO (hPutStrLn stdout s) *> k
  alg (R other)       = TraceC (alg (handleCoercible other))
  {-# INLINE alg #-}
