{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, TypeFamilies #-}
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

class VectorSpace (AVector p) => AffineSpace p where
  -- | Associated vector space
  type AVector p
  -- | Subtract points
  (.-.)  :: p -> p -> AVector p
  -- | Point plus vector
  (.+^)  :: p -> AVector p -> p

-- TODO: consider replacing p and v with a type constructor argument:
-- 
-- class VectorSpace' v => AffineSpace p v | p -> v where
--   (.-.)  :: p s -> p s -> v s
--   (.+^)  :: p s -> v s -> p s
-- 
-- Perhaps with constraints on s.  We couldn't then define instances for
-- doubles & floats.

-- | Point minus vector
(.-^) :: (AffineSpace p) => p -> AVector p -> p
p .-^ v = p .+^ negateV v

-- | Square of the distance between two points.  Sometimes useful for
-- efficiency.  See also 'distance'.
distanceSq :: (AffineSpace p, v ~ AVector p, InnerSpace v) =>
              p -> p -> Scalar v
distanceSq = (fmap.fmap) magnitudeSq (.-.)

-- | Distance between two points.  See also 'distanceSq'.
distance :: (AffineSpace p, v ~ AVector p, InnerSpace v
            , s ~ Scalar v, Floating (Scalar v))
         => p -> p -> s
distance = (fmap.fmap) sqrt distanceSq

-- | Affine linear interpolation.  Varies from @p@ to @p'@ as @s@ varies
-- from 0 to 1.  See also 'lerp' (on vector spaces).
alerp :: AffineSpace p => p -> p -> Scalar (AVector p) -> p
alerp p p' s = p .+^ (s *^ (p' .-. p))

instance  AffineSpace Double where
  type AVector Double = Double
  (.-.) =  (-)
  (.+^) =  (+)

instance  AffineSpace Float where
  type AVector Float = Float
  (.-.) =  (-)
  (.+^) =  (+)

-- TODO: pairs & triples.  Functions?

