{-# LANGUAGE FlexibleInstances, TypeOperators, UndecidableInstances
           , TypeSynonymInstances
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
import Data.LinearMap
import Data.Derivative

-- | Thing with a normal vector (not necessarily normalized).
class HasNormal v where normalVec :: v -> v

-- | Normalized normal vector.  See also 'cross'.
normal :: (HasNormal v, InnerSpace v s, Floating s) => v -> v
normal = normalized . normalVec


-- | Singleton
type One   s = s

-- | Homogeneous pair
type Two   s = (s,s)

-- | Homogeneous triple
type Three s = (s,s,s)

-- | Cross product of various forms of 2D vectors
class HasCross2 v where cross2 :: v -> v

instance Num s => HasCross2 (s,s) where
  cross2 (x,y) = (-y,x)  -- or @(y,-x)@?

-- TODO: Eliminate the 'Num' constraint by using negateV.

-- "Variable occurs more often in a constraint than in the instance
-- head".  Hence UndecidableInstances.

instance (LMapDom a s, VectorSpace v s, HasCross2 v) => HasCross2 (a:>v) where
  -- 2d cross-product is linear
  cross2 = fmapD cross2

instance (Num s, LMapDom s s) => HasNormal (One s :> Two s) where
  normalVec v = cross2 (derivativeAt v 1)

-- Does this problem come from the choice of 'VectorSpace' instance?

instance (Num s, LMapDom s s, VectorSpace s s)
    => HasNormal (Two (One s :> s)) where
  normalVec = unpairD . normalVec . pairD


-- | Cross product of various forms of 3D vectors
class HasCross3 v where cross3 :: v -> v -> v

instance Num s => HasCross3 (s,s,s) where
  (ax,ay,az) `cross3` (bx,by,bz) = ( ay * bz - az * by
                                   , az * bx - ax * bz
                                   , ax * by - ay * bx )

-- TODO: Eliminate the 'Num' constraint by using 'VectorSpace' operations.

instance (LMapDom a s, VectorSpace v s, HasCross3 v) => HasCross3 (a:>v) where
  -- 3D cross-product is bilinear (curried linear)
  cross3 = distrib cross3

instance (Num s, LMapDom s s) => HasNormal (Two s :> Three s) where
  normalVec v = d (1,0) `cross3` d (0,1)
   where
     d = derivativeAt v

instance (Num s, VectorSpace s s, LMapDom s s) => HasNormal (Three (Two s :> s)) where
  normalVec = untripleD . normalVec . tripleD

---- Could go elsewhere

pairD :: (LMapDom a s, VectorSpace b s, VectorSpace c s) =>
         (a:>b,a:>c) -> a:>(b,c)
pairD (u,v) = liftD2 (,) u v

tripleD :: (LMapDom a s, VectorSpace b s, VectorSpace c s, VectorSpace d s) =>
           (a:>b,a:>c,a:>d) -> a:>(b,c,d)
tripleD (u,v,w) = liftD3 (,,) u v w

unpairD :: (LMapDom a s, VectorSpace a s, VectorSpace b s, VectorSpace c s) =>
           (a :> (b,c)) -> (a:>b, a:>c)
unpairD d = (fst <$>> d, snd <$>> d)

untripleD :: ( LMapDom a s , VectorSpace a s, VectorSpace b s
             , VectorSpace c s, VectorSpace d s) =>
             (a :> (b,c,d)) -> (a:>b, a:>c, a:>d)
untripleD d =
  ((\ (a,_,_) -> a) <$>> d, (\ (_,b,_) -> b) <$>> d, (\ (_,_,c) -> c) <$>> d)
