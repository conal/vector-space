{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.AffineSpace
-- Copyright   :  (c) Conal Elliott and Andy J Gill 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net, andygill@ku.edu
-- Stability   :  experimental
-- 
-- Affine spaces.
----------------------------------------------------------------------

module Data.AffineSpace
  (
    AffineSpace(..), (.-^), distanceSq, distance, alerp
  ) where

import Data.VectorSpace

infix 4 .+^, .-^, .-.

class VectorSpace v s => AffineSpace p v s | p -> v s where
  -- | Subtract points
  (.-.)  :: p -> p -> v
  -- | Point plus vector
  (.+^)  :: p -> v -> p

-- TODO: consider replacing p and v with a type constructor argument:
-- 
-- class VectorSpace' v => AffineSpace p v | p -> v where
--   (.-.)  :: p s -> p s -> v s
--   (.+^)  :: p s -> v s -> p s
-- 
-- Perhaps with constraints on s.  We couldn't then define instances for
-- doubles & floats.

-- | Point minus vector
(.-^) :: (Num s, AffineSpace p v s) => p -> v -> p
p .-^ v = p .+^ negateV v

-- | Square of the distance between two points.  Sometimes useful for
-- efficiency.  See also 'distance'.
distanceSq :: (AffineSpace p v s, InnerSpace v s) => p -> p -> s
distanceSq = (fmap.fmap) magnitudeSq (.-.)

-- | Distance between two points.  See also 'distanceSq'.
distance :: (Floating s, AffineSpace p v s, InnerSpace v s) => p -> p -> s
distance = (fmap.fmap) sqrt distanceSq

-- | Affine linear interpolation.  Varies from @p@ to @p'@ as @s@ varies
-- from 0 to 1.  See also 'lerp' (on vector spaces).
alerp :: AffineSpace p v s => p -> p -> s -> p
alerp p p' s = p .+^ (s *^ (p' .-. p))

instance  AffineSpace Double Double Double where
  (.-.)  =  (-)
  (.+^)  =  (+)

instance  AffineSpace Float Float Float where
  (.-.)  =  (-)
  (.+^)  =  (+)
