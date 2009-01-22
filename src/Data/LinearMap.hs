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
-- This version uses ABasis, which requires ghc-6.10 or later.
----------------------------------------------------------------------

module Data.LinearMap
  ( (:-*) , linear, lapply
  ) where

import Control.Arrow (first)
import Data.Function

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
