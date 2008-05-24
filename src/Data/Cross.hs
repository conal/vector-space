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
    HasCross(..), normal
  , One, Two, Three
  , HasCross2(..), HasCross3(..)
  ) where

import Control.Applicative

import Data.VectorSpace
import Data.Derivative

-- | Thing with a cross product.
class HasCross v where cross :: v -> v

-- | Normalized normal vector.  See also 'cross.
normal :: (HasCross v, InnerSpace v s, Floating s) => v -> v
normal = normalized . cross


-- | Singleton
type One   s = s

-- | Homogeneous pair
type Two   s = (s,s)

-- | Homogeneous triple
type Three s = (s,s,s)

-- | Cross product of various forms of 2D vectors
class HasCross2 v where cross2 :: v -> v

instance Num s => HasCross2 (s,s) where
  cross2 (x,y) = (-y,x)  -- or @(-y,x)@?

-- TODO: Eliminate the 'Num' constraint by using negateV.

-- "Variable occurs more often in a constraint than in the instance
-- head".  Hence UndecidableInstances.

-- 2d cross-product is linear
instance (VectorSpace v s, HasCross2 v) => HasCross2 (a:>v) where
  cross2 = fmap cross2

instance (Num s, VectorSpace s s) => HasCross (One s :> Two s) where
  cross v = cross2 (deriv v 1)

instance (Num s, VectorSpace s s) => HasCross (Two (One s :> s)) where
  cross = unpairF . cross . pairF



-- | Cross product of various forms of 3D vectors
class HasCross3 v where cross3 :: v -> v -> v

instance Num s => HasCross3 (s,s,s) where
  (ax,ay,az) `cross3` (bx,by,bz) = ( ay * bz - az * by
                                   , az * bx - ax * bz
                                   , ax * by - ay * bx )

-- TODO: Eliminate the 'Num' constraint by using 'VectorSpace' operations.


-- 3D cross-product is bilinear
instance (VectorSpace v s, HasCross3 v) => HasCross3 (a:>v) where
  cross3 = distribD cross3 cross3

instance (Num s, VectorSpace s s) => HasCross (Two s :> Three s) where
  cross v = v' (1,0) `cross3` v' (0,1)
   where
     v' = dDeriv v

instance (Num s, VectorSpace s s) => HasCross (Three (Two s :> s)) where
  cross = untripleF . cross . tripleF


---- Could go elsewhere

pairF :: (Applicative f) => (f a, f b) -> f (a, b)
pairF (u,v) = liftA2 (,) u v

tripleF :: (Applicative f) => (f a, f b, f c) -> f (a, b, c)
tripleF (u,v,w) = liftA3 (,,) u v w

unpairF :: (Functor f) => f (a, b) -> (f a, f b)
unpairF d = (fst <$> d, snd <$> d)

untripleF :: (Functor f) => f (a, b, c) -> (f a, f b, f c)
untripleF d =
  ((\ (a,_,_) -> a) <$> d, (\ (_,b,_) -> b) <$> d, (\ (_,_,c) -> c) <$> d)

-- Hm.  Note how unpairF an untripleF
