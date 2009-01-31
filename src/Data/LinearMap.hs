{-# LANGUAGE TypeOperators, FlexibleContexts, TypeFamilies, CPP #-}
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
  ) where

import Control.Applicative ((<$>),liftA2)
import Control.Arrow       (first)

import Data.MemoTrie       ((:->:)(..))
import Data.VectorSpace    (AdditiveGroup(..), VectorSpace(..))
import Data.Basis          (HasBasis(..), linearCombo)


-- Linear maps are almost but not quite a Control.Category.  The type
-- class constraints interfere.  They're almost an Arrow also, but for the
-- constraints and the generality of arr.

-- | Linear map, represented as an optional memo-trie from basis to
-- values, where 'Nothing' means the zero map (an optimization).
type u :-* v = Maybe (Basis u :->: v)


-- TODO: Use a regular function from @Basis u@, but memoize it.

-- | Function (assumed linear) as linear map.
linear :: (HasBasis u, HasTrie (Basis u)) =>
          (u -> v) -> (u :-* v)
linear f = Just (trie (f . basisValue))

atZ :: AdditiveGroup b => (a -> b) -> (Maybe a -> b)
atZ = maybe zeroV

-- | Evaluate a linear map on a basis element.  I've loosened the type to
-- work around a typing problem in 'derivAtBasis'.
-- atBasis :: (AdditiveGroup v, HasTrie (Basis u)) =>
--            (u :-* v) -> Basis u -> v
atBasis :: (HasTrie a, AdditiveGroup b) => Maybe (a :->: b) -> a -> b
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

-- Nothing *.* _       = Nothing
-- _ *.* Nothing       = Nothing
-- Just vw *.* Just uv = Just (lapply' vw <$> uv)

(*.*) = liftA2 (\ vw uv -> lapply' vw <$> uv)

-- (*.*) = liftA2 (\ vw -> fmap (lapply' vw))

-- (*.*) = liftA2 (fmap . lapply')


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
