{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts
           , FunctionalDependencies #-}
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

-- TODO: Convert AffineSpace from fundep to associated type, and eliminate
-- FunctionalDependencies above.

class VectorSpace v => AffineSpace p v | p -> v where
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
(.-^) :: (AffineSpace p v) => p -> v -> p
p .-^ v = p .+^ negateV v

-- | Square of the distance between two points.  Sometimes useful for
-- efficiency.  See also 'distance'.
distanceSq :: (AffineSpace p v, InnerSpace v) => p -> p -> Scalar v
distanceSq = (fmap.fmap) magnitudeSq (.-.)

-- | Distance between two points.  See also 'distanceSq'.
distance :: (AffineSpace p v, InnerSpace v, Floating (Scalar v))
         => p -> p -> Scalar v
distance = (fmap.fmap) sqrt distanceSq

-- | Affine linear interpolation.  Varies from @p@ to @p'@ as @s@ varies
-- from 0 to 1.  See also 'lerp' (on vector spaces).
alerp :: AffineSpace p v => p -> p -> Scalar v -> p
alerp p p' s = p .+^ (s *^ (p' .-. p))

instance  AffineSpace Double Double where
  (.-.)  =  (-)
  (.+^)  =  (+)

instance  AffineSpace Float Float where
  (.-.)  =  (-)
  (.+^)  =  (+)

-- TODO: pairs & triples.  Functions?

