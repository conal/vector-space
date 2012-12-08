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
    AffineSpace(..), (.-^), distanceSq, distance, alerp
  ) where

import Control.Applicative (liftA2)
import Data.Ratio
import Foreign.C.Types (CFloat, CDouble)

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
