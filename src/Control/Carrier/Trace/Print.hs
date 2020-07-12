-- This is basically taken from the ReaderC implementation of `fused-effects`

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}

module Control.Carrier.Trace.Print
  ( runTracePrint
  , runTraceIgnore
  , TraceC
  , module Control.Effect.Trace
  ) where

import Control.Algebra
import Control.Applicative (Alternative(..), liftA2)
import Control.Effect.Trace
import Control.Monad (MonadPlus(..))
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import System.IO

runTracePrint :: TraceC m a -> m a
runTracePrint = runTrace (Just stdout)

runTraceIgnore :: TraceC m a -> m a
runTraceIgnore = runTrace Nothing

runTrace :: Maybe Handle -> TraceC m a -> m a
runTrace b (TraceC f) = f b

newtype TraceC m a = TraceC (Maybe Handle -> m a)
  deriving (Functor)

instance Applicative m => Applicative (TraceC m) where
  pure = TraceC . const . pure
  {-# INLINE pure #-}

  TraceC m1 <*> TraceC m2 = TraceC (\b -> m1 b <*> m2 b)
  {-# INLINE (<*>) #-}

  TraceC m1 <* TraceC m2 = TraceC (\b -> m1 b <* m2 b)
  {-# INLINE (<*) #-}

  TraceC m1 *> TraceC m2 = TraceC (\b -> m1 b *> m2 b)
  {-# INLINE (*>) #-}

instance Monad m => Monad (TraceC m) where
  TraceC a >>= f = TraceC (\ b -> a b >>= runTrace b . f)
  {-# INLINE (>>=) #-}

instance MonadIO m => MonadIO (TraceC m) where
  liftIO = TraceC . const . liftIO
  {-# INLINE liftIO #-}

instance Alternative m => Alternative (TraceC m) where
  empty = TraceC (const empty)
  {-# INLINE empty #-}

  TraceC l <|> TraceC r = TraceC (liftA2 (<|>) l r)
  {-# INLINE (<|>) #-}

instance (Alternative m, Monad m) => MonadPlus (TraceC m)

instance MonadTrans TraceC where
  lift = TraceC . const
  {-# INLINE lift #-}

instance (MonadIO m, Algebra sig m) => Algebra (Trace :+: sig) (TraceC m) where
  -- alg hdl (L (Trace s)) = TraceC prnt
  --   where prnt Nothing  = return ()
  --         prnt (Just h) = liftIO $ hPutStrLn h s
  -- alg hdl (R other) ctx = TraceC (\b -> alg (hmap (runTrace b) other))
  alg _hdl (L (Trace s)) ctx = TraceC prnt
    where prnt Nothing  = ctx <$ return ()
          prnt (Just h) = ctx <$ liftIO (hPutStrLn h s)

  alg hdl (R other) ctx = TraceC (\b -> (alg ((runTrace b) . hdl) other ctx))
  {-# INLINE alg #-}
