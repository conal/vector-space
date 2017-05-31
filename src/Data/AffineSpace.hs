{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, TypeFamilies, CPP #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric        #-}
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
import Foreign.C.Types (CSChar, CInt, CShort, CLong, CLLong, CIntMax, CFloat, CDouble)
import Control.Arrow(first)

import Data.VectorSpace
import Data.Basis

import Data.VectorSpace.Generic
import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)(..))

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
  type Diff p = GenericDiff p
  -- | Subtract points
  (.-.)  :: p -> p -> Diff p
  default (.-.) :: ( Generic p, Diff p ~ GenericDiff p, AffineSpace (VRep p) )
              => p -> p -> Diff p
  p .-. q = GenericDiff
         $ (Gnrx.from p .-. (Gnrx.from q :: VRep p))
  -- | Point plus vector
  (.+^)  :: p -> Diff p -> p
  default (.+^) :: ( Generic p, Diff p ~ GenericDiff p, AffineSpace (VRep p) )
              => p -> Diff p -> p
  p .+^ GenericDiff q = Gnrx.to (Gnrx.from p .+^ q :: VRep p)

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

ScalarType(Int)
ScalarType(Integer)
ScalarType(Double)
ScalarType(Float)
ScalarType(CSChar)
ScalarType(CInt)
ScalarType(CShort)
ScalarType(CLong)
ScalarType(CLLong)
ScalarType(CIntMax)
ScalarType(CDouble)
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



newtype GenericDiff p = GenericDiff (Diff (VRep p))
       deriving (Generic)

instance AdditiveGroup (Diff (VRep p)) => AdditiveGroup (GenericDiff p)
instance VectorSpace (Diff (VRep p)) => VectorSpace (GenericDiff p)
instance InnerSpace (Diff (VRep p)) => InnerSpace (GenericDiff p)
instance HasBasis (Diff (VRep p)) => HasBasis (GenericDiff p)

data AffineDiffProductSpace f g p = AffineDiffProductSpace
            !(Diff (f p)) !(Diff (g p)) deriving (Generic)
instance (AffineSpace (f p), AffineSpace (g p))
    => AdditiveGroup (AffineDiffProductSpace f g p)
instance ( AffineSpace (f p), AffineSpace (g p)
         , VectorSpace (Diff (f p)), VectorSpace (Diff (g p))
         , Scalar (Diff (f p)) ~ Scalar (Diff (g p)) )
    => VectorSpace (AffineDiffProductSpace f g p)
instance ( AffineSpace (f p), AffineSpace (g p)
         , InnerSpace (Diff (f p)), InnerSpace (Diff (g p))
         , Scalar (Diff (f p)) ~ Scalar (Diff (g p))
         , Num (Scalar (Diff (f p))) )
    => InnerSpace (AffineDiffProductSpace f g p)
instance (AffineSpace (f p), AffineSpace (g p))
    => AffineSpace (AffineDiffProductSpace f g p) where
  type Diff (AffineDiffProductSpace f g p) = AffineDiffProductSpace f g p
  (.+^) = (^+^)
  (.-.) = (^-^)
instance ( AffineSpace (f p), AffineSpace (g p)
         , HasBasis (Diff (f p)), HasBasis (Diff (g p))
         , Scalar (Diff (f p)) ~ Scalar (Diff (g p)) )
    => HasBasis (AffineDiffProductSpace f g p) where
  type Basis (AffineDiffProductSpace f g p) = Either (Basis (Diff (f p)))
                                                     (Basis (Diff (g p)))
  basisValue (Left bf) = AffineDiffProductSpace (basisValue bf) zeroV
  basisValue (Right bg) = AffineDiffProductSpace zeroV (basisValue bg)
  decompose (AffineDiffProductSpace vf vg)
        = map (first Left) (decompose vf) ++ map (first Right) (decompose vg)
  decompose' (AffineDiffProductSpace vf _) (Left bf) = decompose' vf bf
  decompose' (AffineDiffProductSpace _ vg) (Right bg) = decompose' vg bg


instance AffineSpace a => AffineSpace (Gnrx.Rec0 a s) where
  type Diff (Gnrx.Rec0 a s) = Diff a
  Gnrx.K1 v .+^ w = Gnrx.K1 $ v .+^ w
  Gnrx.K1 v .-. Gnrx.K1 w = v .-. w
instance AffineSpace (f p) => AffineSpace (Gnrx.M1 i c f p) where
  type Diff (Gnrx.M1 i c f p) = Diff (f p)
  Gnrx.M1 v .+^ w = Gnrx.M1 $ v .+^ w
  Gnrx.M1 v .-. Gnrx.M1 w = v .-. w
instance (AffineSpace (f p), AffineSpace (g p)) => AffineSpace ((f :*: g) p) where
  type Diff ((f:*:g) p) = AffineDiffProductSpace f g p
  (x:*:y) .+^ AffineDiffProductSpace ξ υ = (x.+^ξ) :*: (y.+^υ)
  (x:*:y) .-. (ξ:*:υ) = AffineDiffProductSpace (x.-.ξ) (y.-.υ)
