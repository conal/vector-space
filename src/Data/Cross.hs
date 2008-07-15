{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeOperators, UndecidableInstances
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

-- import Data.LinearMap
import Data.Derivative
-- import Data.Maclaurin

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

instance AdditiveGroup u => HasCross2 (u,u) where
  cross2 (x,y) = (negateV y,x)  -- or @(y,-x)@?

-- "Variable occurs more often in a constraint than in the instance
-- head".  Hence UndecidableInstances.

instance ( HasBasis a s, HasTrie (Basis a)
         , VectorSpace v s, HasCross2 v) => HasCross2 (a:>v) where
  -- 2d cross-product is linear
  cross2 = fmapD cross2

instance HasNormal (One Float :> Two Float) where
  normalVec v = cross2 (derivative v `untrie` ())

instance HasNormal (One Double :> Two Double) where
  normalVec v = cross2 (derivative v `untrie` ())

-- TODO: can these two instances be subsumed by a single instance with an
-- type equality constraint?
-- 
--   instance (HasBasis v s, HasTrie (Basis v), Basis v ~ ()) =>
--            HasNormal (One v :> Two v) where
--     normalVec v = cross2 (derivative v `untrie` ())
-- 
-- Result:
-- 
--   ghc.exe: panic! (the 'impossible' happened)

-- instance (Num s, HasBasis s s, HasTrie (Basis s), VectorSpace s s)
--     => HasNormal (Two (One s :> s)) where
--   normalVec = unpairD . normalVec . pairD

instance HasNormal (Two (One Float :> Float)) where
  normalVec = unpairD . normalVec . pairD

instance HasNormal (Two (One Double :> Double)) where
  normalVec = unpairD . normalVec . pairD


-- | Cross product of various forms of 3D vectors
class HasCross3 v where cross3 :: v -> v -> v

instance Num s => HasCross3 (s,s,s) where
  (ax,ay,az) `cross3` (bx,by,bz) = ( ay * bz - az * by
                                   , az * bx - ax * bz
                                   , ax * by - ay * bx )

-- TODO: Eliminate the 'Num' constraint by using 'VectorSpace' operations.

instance (HasBasis a s, HasTrie (Basis a), VectorSpace v s, HasCross3 v) => HasCross3 (a:>v) where
  -- 3D cross-product is bilinear (curried linear)
  cross3 = distrib cross3

-- instance (Num s, HasTrie (Basis (s, s)), HasBasis s s) =>
--          HasNormal (Two s :> Three s) where
--   normalVec v = d (Left ()) `cross3` d (Right ())
--    where
--      d = untrie (derivative v)

instance HasNormal (Two Float :> Three Float) where
  normalVec v = d (Left ()) `cross3` d (Right ())
   where
     d = untrie (derivative v)

instance HasNormal (Two Double :> Three Double) where
  normalVec v = d (Left ()) `cross3` d (Right ())
   where
     d = untrie (derivative v)

instance ( Num s, VectorSpace s s, HasBasis s s, HasTrie (Basis s)
         , HasNormal (Two s :> Three s))
         => HasNormal (Three (Two s :> s)) where
  normalVec = untripleD . normalVec . tripleD

-- instance HasNormal (Three (Two Float :> Float)) where
--   normalVec = untripleD . normalVec . tripleD

-- instance HasNormal (Three (Two Double :> Double)) where
--   normalVec = untripleD . normalVec . tripleD

---- Could go elsewhere

pairD :: (HasBasis a s, HasTrie (Basis a), VectorSpace b s, VectorSpace c s) =>
         (a:>b,a:>c) -> a:>(b,c)
pairD (u,v) = liftD2 (,) u v

tripleD :: (HasBasis a s, HasTrie (Basis a), VectorSpace b s, VectorSpace c s, VectorSpace d s) =>
           (a:>b,a:>c,a:>d) -> a:>(b,c,d)
tripleD (u,v,w) = liftD3 (,,) u v w

unpairD :: (HasBasis a s, HasTrie (Basis a), VectorSpace a s, VectorSpace b s, VectorSpace c s) =>
           (a :> (b,c)) -> (a:>b, a:>c)
unpairD d = (fst <$>> d, snd <$>> d)

untripleD :: ( HasBasis a s, HasTrie (Basis a) , VectorSpace a s, VectorSpace b s
             , VectorSpace c s, VectorSpace d s) =>
             (a :> (b,c,d)) -> (a:>b, a:>c, a:>d)
untripleD d =
  ((\ (a,_,_) -> a) <$>> d, (\ (_,b,_) -> b) <$>> d, (\ (_,_,c) -> c) <$>> d)
