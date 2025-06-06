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
  , liftMS, liftMS2, liftMS3
  , liftL, liftL2, liftL3
  ) where

import Control.Applicative ((<$>),Applicative,liftA2,liftA3)
import Control.Arrow       (first)

import Data.MemoTrie      ((:->:)(..))
import Data.AdditiveGroup (Sum(..),inSum2, AdditiveGroup(..))
import Data.VectorSpace   (VectorSpace(..))
import Data.Basis         (HasBasis(..), linearCombo)


-- Linear maps are almost but not quite a Control.Category.  The type
-- class constraints interfere.  They're almost an Arrow also, but for the
-- constraints and the generality of arr.

-- | An optional additive value
type MSum a = Maybe (Sum a)

-- nsum :: MSum a
-- nsum = Nothing

jsum :: a -> MSum a
jsum = Just . Sum

-- | Linear map, represented as an optional memo-trie from basis to
-- values, where 'Nothing' means the zero map (an optimization).
type u :-* v = MSum (Basis u :->: v)

-- TODO: Try a partial trie instead, excluding (known) zero elements.
-- Then 'lapply' could be much faster for sparse situations.  Make sure to
-- correctly sum them.  It'd be more like Jason Foutz's formulation
-- <http://metavar.blogspot.com/2008/02/higher-order-multivariate-automatic.html>
-- which uses in @IntMap@.


-- PROBLEM: u :-* v is a type synonym, and Basis is an associated type synonym, resulting in a subtle
-- ambiguity: u:-*v == u':-*v' does not imply that u==u', since Basis
-- might map different types to the same basis (e.g., Float & Double).
-- See <http://hackage.haskell.org/trac/ghc/ticket/1897>
--
-- Work in progress.  See NewLinearMap.hs


-- | Function (assumed linear) as linear map.
linear :: (HasBasis u, HasTrie (Basis u)) =>
          (u -> v) -> (u :-* v)
linear f = jsum (trie (f . basisValue))

atZ :: AdditiveGroup b => (a -> b) -> (MSum a -> b)
atZ f = maybe zeroV (f . getSum)

-- atZ :: AdditiveGroup b => (a -> b) -> (a -> b)
-- atZ = id

-- | Evaluate a linear map on a basis element.  I've loosened the type to
-- work around a typing problem in 'derivAtBasis'.
-- atBasis :: (AdditiveGroup v, HasTrie (Basis u)) =>
--            (u :-* v) -> Basis u -> v
atBasis :: (HasTrie a, AdditiveGroup b) => MSum (a :->: b) -> a -> b
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
         , VectorSpace w
         , Scalar v ~ Scalar w ) =>
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

-- (*.*) = (liftA2.inSum2) (\ vw uv -> lapply' vw <$> uv)
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
       -> (MSum a -> MSum b)
-- liftMS _ Nothing = Nothing
-- liftMS h ma = Just (Sum (h (z ma)))

liftMS = fmap.fmap

liftMS2 :: (AdditiveGroup a, AdditiveGroup b) =>
           (a -> b -> c) ->
           (MSum a -> MSum b -> MSum c)
liftMS2 _ Nothing Nothing = Nothing
liftMS2 h ma mb = Just (Sum (h (fromMS ma) (fromMS mb)))

liftMS3 :: (AdditiveGroup a, AdditiveGroup b, AdditiveGroup c) =>
           (a -> b -> c -> d) ->
           (MSum a -> MSum b -> MSum c -> MSum d)
liftMS3 _ Nothing Nothing Nothing = Nothing
liftMS3 h ma mb mc = Just (Sum (h (fromMS ma) (fromMS mb) (fromMS mc)))

fromMS :: AdditiveGroup u => MSum u -> u
fromMS Nothing        = zeroV
fromMS (Just (Sum u)) = u


-- | Apply a linear function to each element of a linear map.
-- @liftL f l == linear f *.* l@, but works more efficiently.
liftL :: (Functor f, AdditiveGroup (f a)) =>
         (a -> b) -> MSum (f a) -> MSum (f b)
liftL = liftMS . fmap

-- | Apply a linear binary function (not to be confused with a bilinear
-- function) to each element of a linear map.
liftL2 :: (Applicative f, AdditiveGroup (f a), AdditiveGroup (f b)) =>
          (a -> b -> c)
       -> (MSum (f a) -> MSum (f b) -> MSum (f c))
liftL2 = liftMS2 . liftA2

-- | Apply a linear ternary function (not to be confused with a trilinear
-- function) to each element of a linear map.
liftL3 :: ( Applicative f
          , AdditiveGroup (f a), AdditiveGroup (f b), AdditiveGroup (f c)) =>
          (a -> b -> c -> d)
       -> (MSum (f a) -> MSum (f b) -> MSum (f c) -> MSum (f d))
liftL3 = liftMS3 . liftA3
