{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeOperators
           , TypeFamilies, TypeSynonymInstances
  #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Cross
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Cross products and normals
----------------------------------------------------------------------

module Data.Cross
  (
    HasNormal(..), normal
  , One, Two, Three
  , HasCross2(..), HasCross3(..)
  ) where

import Data.VectorSpace
import Data.MemoTrie
import Data.Basis

import Data.Derivative

-- | Thing with a normal vector (not necessarily normalized).
class HasNormal v where normalVec :: v -> v

-- | Normalized normal vector.  See also 'cross'.
normal :: (HasNormal v, InnerSpace v, Floating (Scalar v)) => v -> v
normal = normalized . normalVec

-- | Singleton
type One   s = s

-- | Homogeneous pair
type Two   s = (s,s)

-- | Homogeneous triple
type Three s = (s,s,s)

-- | Cross product of various forms of 2D vectors
class HasCross2 v where cross2 :: v -> v

instance AdditiveGroup u => HasCross2 (u,u) where
  cross2 (x,y) = (negateV y,x)  -- or @(y,-x)@?

instance ( HasBasis a, HasTrie (Basis a)
         , VectorSpace v, HasCross2 v) => HasCross2 (a:>v) where
  -- 2d cross-product is linear
  cross2 = fmapD cross2

instance (HasBasis s, HasTrie (Basis s), Basis s ~ ()) =>
         HasNormal (One s :> Two s) where
  normalVec v = cross2 (v `derivAtBasis` ())

-- When I use atBasis (from LinearMap) instead of the more liberally-typed
-- atB (below), I get a type error:
-- 
--     Couldn't match expected type `Basis a1' against inferred type `()'
--       Expected type: a1 :-* (s :> Two s)
--       Inferred type: s  :-* (s :> Two s)
--     In the first argument of `atB', namely `derivative v'
-- 
-- I think this type error is a GHC bug, but I'm not sure.

-- atB :: (AdditiveGroup b, HasTrie a) => Maybe (a :->: b) -> a -> b
-- -- atB :: (AdditiveGroup b, HasBasis a, HasTrie (Basis a)) =>
-- --        Maybe (Basis a :->: b) -> Basis a -> b
-- l `atB` b = maybe zeroV (`untrie` b) l


instance ( Num s, VectorSpace s
         , HasBasis s, HasTrie (Basis s), Basis s ~ ())
    => HasNormal (Two (One s :> s)) where
  normalVec = unpairD . normalVec . pairD

-- I don't know why I can't eliminate the @HasTrie (Basis s)@ constraints
-- above, considering @Basis s ~ ()@ and @HasTrie ()@.

-- | Cross product of various forms of 3D vectors
class HasCross3 v where cross3 :: v -> v -> v

instance Num s => HasCross3 (s,s,s) where
  (ax,ay,az) `cross3` (bx,by,bz) = ( ay * bz - az * by
                                   , az * bx - ax * bz
                                   , ax * by - ay * bx )

-- TODO: Eliminate the 'Num' constraint by using 'VectorSpace' operations.

instance (HasBasis a, HasTrie (Basis a), VectorSpace v, HasCross3 v) => HasCross3 (a:>v) where
  -- 3D cross-product is bilinear (curried linear)
  cross3 = distrib cross3

instance (Num s, HasTrie (Basis (s, s)), HasBasis s, Basis s ~ ()) =>
         HasNormal (Two s :> Three s) where
  normalVec v = d (Left ()) `cross3` d (Right ())
   where
     d = derivAtBasis v

instance ( Num s, VectorSpace s, HasBasis s, HasTrie (Basis s)
         , HasNormal (Two s :> Three s))
         => HasNormal (Three (Two s :> s)) where
  normalVec = untripleD . normalVec . tripleD
