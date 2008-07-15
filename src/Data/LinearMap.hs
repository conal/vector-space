{-# LANGUAGE TypeOperators, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
-- {-# OPTIONS_GHC -fglasgow-exts -funbox-strict-fields #-}
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
  ( (:-*) , linear, lapply
  -- , inL, inL2, inL3
  ) where

-- -fglasgow-exts above enables the RULES pragma

import Data.Function

import Data.VectorSpace
import Data.MemoTrie
import Data.Basis


-- | Linear map, represented a as a memo function from basis to values.
type u :-* v = Basis u :->: v

-- | Function (assumed linear) as linear map.
linear :: (VectorSpace u s, VectorSpace v s', HasBasis u s, HasTrie (Basis u)) =>
          (u -> v) -> (u :-* v)
linear f = trie (f . basisValue)

-- | Apply a linear map to a vector.
lapply :: (VectorSpace u s, VectorSpace v s, HasBasis u s, HasTrie (Basis u)) =>
          (u :-* v) -> (u -> v)
lapply lm u = sumV [s *^ (lm `untrie` b) | (s,b) <- decompose u]


-- TODO: unfst, unsnd, pair, unpair


---- OpenGL stuff.

-- I'd rather this code be in a different package.  It's here as a
-- temporary bug workaround.  In ghc-6.8.2, I get the following error
-- message if the 'LMapDom' instance (below) is compiled in a separate
-- module.
-- 
--     Type indexes must match class instance head
--     Found o but expected Vector2 u
--     In the associated type instance for `:-*'
--     In the instance declaration for `LMapDom (Vector2 u) s'
