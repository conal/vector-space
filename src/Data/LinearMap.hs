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
  ( (:-*) , linear, lapply, idL, compL
  ) where

import Control.Arrow (first)

import Data.MemoTrie    ((:->:)(..))
import Data.VectorSpace (VectorSpace(..))
import Data.Basis       (HasBasis(..), linearCombo)


-- Linear maps are almost but not quite a Control.Category.  The type
-- class constraints interfere.  They're almost an Arrow also, but for the
-- constraints and the generality of arr.

-- | Linear map, represented as a memo-trie from basis to values.
type u :-* v = Basis u :->: v


-- TODO: Use a regular function from @Basis u@, but memoize it.

-- | Function (assumed linear) as linear map.
linear :: (HasBasis u, HasTrie (Basis u)) =>
          (u -> v) -> (u :-* v)
linear f = trie (f . basisValue)

-- | Apply a linear map to a vector.
lapply :: ( VectorSpace v, Scalar u ~ Scalar v
          , HasBasis u, HasTrie (Basis u) ) =>
          (u :-* v) -> (u -> v)
lapply tr = linearCombo . fmap (first (untrie tr)) . decompose


-- Identity linear map
idL :: (HasBasis u, HasTrie (Basis u)) => 
       u :-* u
idL = linear id

-- | Compose linear maps
compL :: ( HasBasis u, HasTrie (Basis u)
         , HasBasis v, HasTrie (Basis v)
         , VectorSpace w, Scalar v ~ Scalar w ) =>
         (v :-* w) -> (u :-* v) -> (u :-* w)

compL vw = fmap (lapply vw)

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
