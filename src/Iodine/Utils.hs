{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Iodine.Utils where

import           Iodine.Types

import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import           Data.Hashable
import qualified Data.HashSet as HS
import qualified Data.Sequence as SQ
import           Polysemy
import           Polysemy.Error

combine :: (Monad f, Monoid m, Traversable t) => (a -> f m) -> t a -> f m
combine act as = foldl' (<>) mempty <$> traverse act as

mfold :: (Foldable f, Monoid m) => (a -> m) -> f a -> m
mfold f = foldl' (\ms a -> f a <> ms) mempty

mfoldM :: (Foldable f, Monoid o, Monad m) => (a -> m o) -> f a -> m o
mfoldM f as = foldlM' mempty as $ \acc a -> mappend acc <$> f a

intersects :: HS.HashSet Id -> HS.HashSet Id -> Bool
intersects s1 s2 = go (HS.toList s1)
 where
  go []       = False
  go (a : as) = HS.member a s2 || go as

notSupported :: a
notSupported = error "not supported"

notSupportedM :: Member (Error IodineException) r => Sem r a
notSupportedM = throw (IE NotSupported "")

infixl 9 ||>
(||>) :: Applicative f => f (L a) -> f a -> f (L a)
(||>) fas fa = (|>) <$> fas <*> fa

infixl 9 <||>
(<||>) :: Applicative f => f (L a) -> f (L a) -> f (L a)
(<||>) = liftA2 (<>)

(|:>) :: (Snoc s s a a, Monoid s) => a -> a -> s
(|:>) a1 a2 = mempty |> a1 |> a2

uncurry2 :: (a -> b -> c) -> (a, b) -> c
uncurry2 f (a, b) = f a b

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

curry2 :: ((a, b) -> c) -> (a -> b -> c)
curry2 f a b = f (a, b)

curry3 ::((a, b, c) -> d) -> (a -> b -> c -> d)
curry3 f a b c = f (a, b, c)

assert :: Member (Error IodineException) r
       => Bool                  -- ^ condition to check
       -> String                -- ^ error message
       -> Sem r ()
assert cond msg = unless cond $ throw (IE Assert msg)

foldlM' :: (Foldable t, Monad m)
       => b -> t a -> (b -> a -> m b) -> m b
foldlM' b as act = foldlM act b as

class Monoid (m a) => LiftToMonoid m a where
  liftToMonoid :: a -> m a

instance LiftToMonoid SQ.Seq a where
  liftToMonoid = SQ.singleton

instance LiftToMonoid [] a where
  liftToMonoid = (: [])

instance (Hashable a, Eq a) => LiftToMonoid HS.HashSet a where
  liftToMonoid = HS.singleton

maybeToMonoid :: LiftToMonoid m a => Maybe a -> m a
maybeToMonoid (Just a) = liftToMonoid a
maybeToMonoid Nothing  = mempty

catMaybes' :: (Foldable t, LiftToMonoid t a) => t (Maybe a) -> t a
catMaybes' = foldl' (\acc -> maybe acc (mappend acc . liftToMonoid)) mempty

toSequence :: Foldable t => t a -> L a
toSequence = foldl' (|>) mempty
