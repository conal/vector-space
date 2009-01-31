{-# LANGUAGE TypeOperators, FlexibleContexts, TypeFamilies #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
-- {-# OPTIONS_GHC -funbox-strict-fields #-}
-- {-# OPTIONS_GHC -ddump-simpl-stats -ddump-simpl #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.LinearMap
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Linear maps
----------------------------------------------------------------------

module Data.LinearMap
  ( (:-*) , linear, lapply, atBasis, idL, (*.*)
  , liftMS, liftMS2, liftMS3  -- to remove
  , liftL, liftL2, liftL3
  ) where

import Control.Applicative ((<$>),liftA2,liftA3)
import Control.Arrow       (first)

import Data.MemoTrie      ((:->:)(..))
import Data.AdditiveGroup (Sum(..),inSum2, AdditiveGroup(..))
import Data.VectorSpace   (VectorSpace(..))
import Data.Basis         (HasBasis(..), linearCombo)


-- Linear maps are almost but not quite a Control.Category.  The type
-- class constraints interfere.  They're almost an Arrow also, but for the
-- constraints and the generality of arr.

-- | Linear map, represented as an optional memo-trie from basis to
-- values, where 'Nothing' means the zero map (an optimization).

type u :-* v = Maybe (Sum (Basis u :->: v))

-- TODO: Try a partial trie instead, excluding (known) zero elements.
-- Then 'lapply' could be much faster for sparse situations.  Make sure to
-- correctly sum them.  It'd be more like Jason Foutz's formulation
-- <http://metavar.blogspot.com/2008/02/higher-order-multivariate-automatic.html>
-- which uses in @IntMap@.



-- | Function (assumed linear) as linear map.
linear :: (HasBasis u, HasTrie (Basis u)) =>
          (u -> v) -> (u :-* v)
linear f = Just (Sum (trie (f . basisValue)))

atZ :: AdditiveGroup b => (a -> b) -> (Maybe (Sum a) -> b)
atZ f = maybe zeroV (f . getSum)

-- atZ :: AdditiveGroup b => (a -> b) -> (a -> b)
-- atZ = id

-- | Evaluate a linear map on a basis element.  I've loosened the type to
-- work around a typing problem in 'derivAtBasis'.
-- atBasis :: (AdditiveGroup v, HasTrie (Basis u)) =>
--            (u :-* v) -> Basis u -> v
atBasis :: (HasTrie a, AdditiveGroup b) => Maybe (Sum (a :->: b)) -> a -> b
m `atBasis` b = atZ (`untrie` b) m

-- | Apply a linear map to a vector.
lapply :: ( VectorSpace v, Scalar u ~ Scalar v
          , HasBasis u, HasTrie (Basis u) ) =>
          (u :-* v) -> (u -> v)
lapply = atZ lapply'

-- Handy for 'lapply' and '(*.*)'.
lapply' :: ( VectorSpace v, Scalar u ~ Scalar v
           , HasBasis u, HasTrie (Basis u) ) =>
           (Basis u :->: v) -> (u -> v)
lapply' tr = linearCombo . fmap (first (untrie tr)) . decompose



-- Identity linear map
idL :: (HasBasis u, HasTrie (Basis u)) => 
       u :-* u
idL = linear id

infixr 9 *.*
-- | Compose linear maps
(*.*) :: ( HasBasis u, HasTrie (Basis u)
         , HasBasis v, HasTrie (Basis v)
         , VectorSpace w, Scalar v ~ Scalar w ) =>
         (v :-* w) -> (u :-* v) -> (u :-* w)

-- Simple definition, but only optimizes out uv == zero
-- 
-- (*.*) vw = (fmap.fmap) (lapply vw)

-- Instead, use Nothing/zero if /either/ map is zeroV (exploiting linearity
-- when uv == zeroV.)

-- Nothing       *.* _             = Nothing
-- _             *.* Nothing       = Nothing
-- Just (Sum vw) *.* Just (Sum uv) = Just (Sum (lapply' vw <$> uv))

-- (*.*) = liftA2 (\ (Sum vw) (Sum uv) -> Sum (lapply' vw <$> uv))

(*.*) = (liftA2.inSum2) (\ vw uv -> lapply' vw <$> uv)

-- (*.*) = (liftA2.inSum2) (\ vw -> fmap (lapply' vw))

-- (*.*) = (liftA2.inSum2) (fmap . lapply')


-- It may be helpful that @lapply vw@ is evaluated just once and not
-- once per uv.  'untrie' can strip off all of its trie constructors.

-- Less efficient definition:
-- 
--   vw `compL` uv = linear (lapply vw . lapply uv)
-- 
--   i.e., compL = inL2 (.)
-- 
-- The problem with these definitions is that basis elements get converted
-- to values and then decomposed, followed by recombination of the
-- results.

liftMS :: (AdditiveGroup a) =>
          (a -> b)
       -> (Maybe (Sum a) -> Maybe (Sum b))
-- liftMS _ Nothing = Nothing
-- liftMS h ma = Just (Sum (h (z ma)))

liftMS = fmap.fmap

liftMS2 :: (AdditiveGroup a, AdditiveGroup b) =>
           (a -> b -> c) ->
           (Maybe (Sum a) -> Maybe (Sum b) -> Maybe (Sum c))
liftMS2 _ Nothing Nothing = Nothing
liftMS2 h ma mb = Just (Sum (h (z ma) (z mb)))

liftMS3 :: (AdditiveGroup a, AdditiveGroup b, AdditiveGroup c) =>
           (a -> b -> c -> d) ->
           (Maybe (Sum a) -> Maybe (Sum b) -> Maybe (Sum c) -> Maybe (Sum d))
liftMS3 _ Nothing Nothing Nothing = Nothing
liftMS3 h ma mb mc = Just (Sum (h (z ma) (z mb) (z mc)))

z :: AdditiveGroup u => Maybe (Sum u) -> u
z Nothing        = zeroV
z (Just (Sum u)) = u


-- type u :-* v = Maybe (Sum (Basis u :->: v))

-- I'd rather keep liftMS* private and export just the liftL* below, but
-- using the liftL* triggers a type checking bug.

liftL :: (HasBasis a, HasTrie (Basis a), AdditiveGroup b) =>
         (b -> c)
      -> ((a :-* b) -> (a :-* c))
liftL = liftMS . fmap

liftL2 :: (HasBasis a, HasTrie (Basis a), AdditiveGroup b, AdditiveGroup c) =>
          (b -> c -> d)
       -> ((a :-* b) -> (a :-* c) -> (a :-* d))
liftL2 = liftMS2 . liftA2

liftL3 :: ( HasBasis a, HasTrie (Basis a)
          , AdditiveGroup b, AdditiveGroup c, AdditiveGroup d) =>
          (b -> c -> d -> e)
       -> ((a :-* b) -> (a :-* c) -> (a :-* d) -> (a :-* e))
liftL3 = liftMS3 . liftA3

