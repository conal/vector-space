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
-- This version uses ABasis, which requires ghc-6.10 or later.
----------------------------------------------------------------------

module Data.LinearMap
  ( (:-*) , linear, lapply, idL, compL
  ) where

import Control.Arrow (first)
-- import Data.Function ()

-- #if __GLASGOW_HASKELL__ >= 609
-- import Control.Category
-- import Prelude hiding ((.), id)
-- #endif

-- import Control.Arrow
-- #if __GLASGOW_HASKELL__ < 610
--                       hiding (pure)
-- #endif


import Data.MemoTrie
import Data.VectorSpace
import Data.Basis


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
lapply lm = linearCombo . fmap (first (untrie lm)) . decompose


-- TODO: try adding some abstraction:
-- 
--   newtype u :-* v = LMap (Basis u :->: v)
-- 
-- and define some operations like
-- 
--   pureL :: v -> (u :-* v)
-- 
-- Then define (:-*) as a Category and Arrow.  There will be some property
-- failure for 'arr' (== 'linear'), since we cannot require linearity of the
-- arguments.
-- 
-- Win: Category gives linear map identity and composition.

-- Maybe also inL, inL2, etc (see journal from 2009-01-22).  How to keep
-- it simple & efficient?

idL :: (HasBasis u, HasTrie (Basis u)) => 
       u :-* u
idL = linear id

-- compL :: ( HasBasis v, HasTrie (Basis v)
--          , HasBasis u, HasTrie (Basis u)
--          , Scalar u ~ Scalar v, Scalar v ~ Scalar w
--          , VectorSpace w
--          ) =>
--          (v :-* w) -> (u :-* v) -> (u :-* w)
-- vw `compL` uv = linear (lapply vw . lapply uv)

-- compL = inL2 (.)

-- More efficient:

compL :: ( HasBasis u, HasTrie (Basis u)
         , HasBasis v, HasTrie (Basis v)
         , VectorSpace w, Scalar v ~ Scalar w ) =>
         (v :-* w) -> (u :-* v) -> (u :-* w)

-- vw `compL` uv = trie (\ e -> vw `lapply` (uv `untrie` e))

-- vw `compL` uv = trie (lapply vw . untrie uv)

-- vw `compL` uv = trie (lapply vw `fmap` untrie uv)

-- compL vw uv = (trie . fmap (lapply vw) . untrie) uv

-- compL vw = trie . fmap (lapply vw) . untrie

-- compL vw = inTrie (fmap (lapply vw))

compL vw = fmap (lapply vw)

-- It may be helpful that @lapply vw@ is evaluated just once and not
-- once per uv.  'untrie' can strip off all of its trie constructors.


-- #if __GLASGOW_HASKELL__ >= 609
-- instance Category (:-*) where
--   id  = idL
--   (.) = compL
-- #endif
