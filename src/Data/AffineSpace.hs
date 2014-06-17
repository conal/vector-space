{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, TypeFamilies, CPP #-}
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
    AffineSpace(..), (.-^), distanceSq, distance, alerp, affineCombo
  ) where

import Control.Applicative (liftA2)
import Data.Ratio
import Foreign.C.Types (CFloat, CDouble)
import Control.Arrow(first)

import Data.VectorSpace

-- Through 0.8.4, I used the following fixities.
-- 
--   infix 4 .+^, .-^, .-.
-- 
-- Changed in 0.8.5 to match precedence of + and -, and to associate usefully.
-- Thanks to Ben Gamari for suggesting left-associativity.

infixl 6 .+^, .-^
infix  6 .-.


-- TODO: Convert AffineSpace from fundep to associated type, and eliminate
-- FunctionalDependencies above.

class AdditiveGroup (Diff p) => AffineSpace p where
  -- | Associated vector space
  type Diff p
  -- | Subtract points
  (.-.)  :: p -> p -> Diff p
  -- | Point plus vector
  (.+^)  :: p -> Diff p -> p

-- | Point minus vector
(.-^) :: AffineSpace p => p -> Diff p -> p
p .-^ v = p .+^ negateV v

-- | Square of the distance between two points.  Sometimes useful for
-- efficiency.  See also 'distance'.
distanceSq :: (AffineSpace p, v ~ Diff p, InnerSpace v) =>
              p -> p -> Scalar v
distanceSq = (fmap.fmap) magnitudeSq (.-.)

-- | Distance between two points.  See also 'distanceSq'.
distance :: (AffineSpace p, v ~ Diff p, InnerSpace v
            , s ~ Scalar v, Floating (Scalar v))
         => p -> p -> s
distance = (fmap.fmap) sqrt distanceSq

-- | Affine linear interpolation.  Varies from @p@ to @p'@ as @s@ varies
-- from 0 to 1.  See also 'lerp' (on vector spaces).
alerp :: (AffineSpace p, VectorSpace (Diff p)) =>
         p -> p -> Scalar (Diff p) -> p
alerp p p' s = p .+^ (s *^ (p' .-. p))

-- | Compute an affine combination (weighted average) of points.
-- The first element is used as origin and is weighted
-- such that all coefficients sum to 1. For example,
--
-- > affineCombo a [(0.3,b), (0.2,c)]
--
-- is equal to
--
-- > a .+^ (0.3 *^ (b .-. a) ^+^ 0.2 *^ (c .-. a))
--
-- and if @a@, @b@, and @c@ were in a vector space would also be equal to
--
-- > 0.5 *^ a ^+^ 0.3 *^ b ^+^ 0.2 *^ c
--
-- See also 'linearCombo' (on vector spaces).
affineCombo :: (AffineSpace p, v ~ Diff p, VectorSpace v) => p -> [(p,Scalar v)] -> p
affineCombo z l = z .+^ linearCombo (map (first (.-. z)) l)

#define ScalarTypeCon(con,t) \
  instance con => AffineSpace (t) where \
    { type Diff (t) = t \
    ; (.-.) = (-) \
    ; (.+^) = (+) }

#define ScalarType(t) ScalarTypeCon((),t)

ScalarType(Double)
ScalarType(CDouble)
ScalarType(Float)
ScalarType(CFloat)
ScalarTypeCon(Integral a,Ratio a)

instance (AffineSpace p, AffineSpace q) => AffineSpace (p,q) where
  type Diff (p,q)   = (Diff p, Diff q)
  (p,q) .-. (p',q') = (p .-. p', q .-. q')
  (p,q) .+^ (u,v)   = (p .+^ u, q .+^ v)

instance (AffineSpace p, AffineSpace q, AffineSpace r) => AffineSpace (p,q,r) where
  type Diff (p,q,r)      = (Diff p, Diff q, Diff r)
  (p,q,r) .-. (p',q',r') = (p .-. p', q .-. q', r .-. r')
  (p,q,r) .+^ (u,v,w)    = (p .+^ u, q .+^ v, r .+^ w)


instance (AffineSpace p) => AffineSpace (a -> p) where
  type Diff (a -> p) = a -> Diff p
  (.-.)              = liftA2 (.-.)
  (.+^)              = liftA2 (.+^)
