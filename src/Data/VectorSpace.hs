{-# LANGUAGE MultiParamTypeClasses, TypeOperators
           , TypeFamilies, UndecidableInstances, CPP
           , FlexibleContexts
 #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :   Data.VectorSpace
-- Copyright   :  (c) Conal Elliott and Andy J Gill 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net, andygill@ku.edu
-- Stability   :  experimental
-- 
-- Vector spaces
-- 
-- This version uses associated types instead of fundeps and
-- requires ghc-6.10 or later
----------------------------------------------------------------------

-- NB: I'm attempting to replace fundeps with associated types.  See
-- NewVectorSpace.hs.  Ran into trouble with type equality constraints not
-- getting propagated.  Manuel Ch is looking into it.
-- 
-- Blocking bug: http://hackage.haskell.org/trac/ghc/ticket/2448

module Data.VectorSpace
  ( module Data.AdditiveGroup
  , VectorSpace(..), (^/), (^*)
  , InnerSpace(..)
  , lerp, magnitudeSq, magnitude, normalized, project
  ) where

import Control.Applicative (liftA2)
import Data.Complex hiding (magnitude)
import Foreign.C.Types (CSChar, CInt, CShort, CLong, CLLong, CIntMax, CFloat, CDouble)
import Data.Ratio

import Data.AdditiveGroup
import Data.MemoTrie

infixr 7 *^

-- | Vector space @v@.
class AdditiveGroup v => VectorSpace v where
  type Scalar v :: *
  -- | Scale a vector
  (*^) :: Scalar v -> v -> v

infixr 7 <.>

-- | Adds inner (dot) products.
class (VectorSpace v, AdditiveGroup (Scalar v)) => InnerSpace v where
  -- | Inner/dot product
  (<.>) :: v -> v -> Scalar v

infixr 7 ^/
infixl 7 ^*

-- | Vector divided by scalar
(^/) :: (VectorSpace v, s ~ Scalar v, Fractional s) => v -> s -> v
v ^/ s = (1/s) *^ v

-- | Vector multiplied by scalar
(^*) :: (VectorSpace v, s ~ Scalar v) => v -> s -> v
(^*) = flip (*^)

-- | Linear interpolation between @a@ (when @t==0@) and @b@ (when @t==1@).

-- lerp :: (VectorSpace v, s ~ Scalar v, Num s) => v -> v -> s -> v
lerp :: VectorSpace v => v -> v -> Scalar v -> v
lerp a b t = a ^+^ t *^ (b ^-^ a)

-- | Square of the length of a vector.  Sometimes useful for efficiency.
-- See also 'magnitude'.
magnitudeSq :: (InnerSpace v, s ~ Scalar v) => v -> s
magnitudeSq v = v <.> v

-- | Length of a vector.   See also 'magnitudeSq'.
magnitude :: (InnerSpace v, s ~ Scalar v, Floating s) =>  v -> s
magnitude = sqrt . magnitudeSq

-- | Vector in same direction as given one but with length of one.  If
-- given the zero vector, then return it.
normalized :: (InnerSpace v, s ~ Scalar v, Floating s) =>  v -> v
normalized v = v ^/ magnitude v

-- | @project u v@ computes the projection of @v@ onto @u@.
project :: (InnerSpace v, s ~ Scalar v, Fractional s) => v -> v -> v
project u v = ((v <.> u) / magnitudeSq u) *^ u

#define ScalarType(t) \
  instance VectorSpace (t) where \
    { type Scalar (t) = (t) \
    ; (*^) = (*) } ; \
  instance InnerSpace  (t) where (<.>) = (*)

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

instance Integral a => VectorSpace (Ratio a) where
  type Scalar (Ratio a) = Ratio a
  (*^) = (*)
instance Integral a => InnerSpace  (Ratio a) where (<.>) = (*)

instance (RealFloat v, VectorSpace v) => VectorSpace (Complex v) where
  type Scalar (Complex v) = Scalar v
  s*^(u :+ v) = s*^u :+ s*^v

instance (RealFloat v, InnerSpace v)
     => InnerSpace (Complex v) where
  (u :+ v) <.> (u' :+ v') = (u <.> u') ^+^ (v <.> v')

-- Hm.  The 'RealFloat' constraint is unfortunate here.  It's due to a
-- questionable decision to place 'RealFloat' into the definition of the
-- 'Complex' /type/, rather than in functions and instances as needed.

-- instance (VectorSpace u,VectorSpace v, s ~ Scalar u, s ~ Scalar v)
--          => VectorSpace (u,v) where
--   type Scalar (u,v) = Scalar u
--   s *^ (u,v) = (s*^u,s*^v)

instance ( VectorSpace u, s ~ Scalar u
         , VectorSpace v, s ~ Scalar v )
      => VectorSpace (u,v) where
  type Scalar (u,v) = Scalar u
  s *^ (u,v) = (s*^u,s*^v)

instance ( InnerSpace u, s ~ Scalar u
         , InnerSpace v, s ~ Scalar v )
    => InnerSpace (u,v) where
  (u,v) <.> (u',v') = (u <.> u') ^+^ (v <.> v')

instance ( VectorSpace u, s ~ Scalar u
         , VectorSpace v, s ~ Scalar v
         , VectorSpace w, s ~ Scalar w )
    => VectorSpace (u,v,w) where
  type Scalar (u,v,w) = Scalar u
  s *^ (u,v,w) = (s*^u,s*^v,s*^w)

instance ( InnerSpace u, s ~ Scalar u
         , InnerSpace v, s ~ Scalar v
         , InnerSpace w, s ~ Scalar w )
    => InnerSpace (u,v,w) where
  (u,v,w) <.> (u',v',w') = u<.>u' ^+^ v<.>v' ^+^ w<.>w'

instance ( VectorSpace u, s ~ Scalar u
         , VectorSpace v, s ~ Scalar v
         , VectorSpace w, s ~ Scalar w
         , VectorSpace x, s ~ Scalar x )
    => VectorSpace (u,v,w,x) where
  type Scalar (u,v,w,x) = Scalar u
  s *^ (u,v,w,x) = (s*^u,s*^v,s*^w,s*^x)

instance ( InnerSpace u, s ~ Scalar u
         , InnerSpace v, s ~ Scalar v
         , InnerSpace w, s ~ Scalar w
         , InnerSpace x, s ~ Scalar x )
    => InnerSpace (u,v,w,x) where
  (u,v,w,x) <.> (u',v',w',x') = u<.>u' ^+^ v<.>v' ^+^ w<.>w' ^+^ x<.>x'


-- Standard instances for a functor applied to a vector space.

-- For 'Maybe', Nothing represents 'zeroV'.  Useful for optimization, since
-- we might not be able to test for 'zeroV', e.g., functions and infinite
-- derivative towers.
instance VectorSpace v => VectorSpace (Maybe v) where
  type Scalar (Maybe v) = Scalar v
  (*^) s = fmap (s *^)

-- instance VectorSpace v => VectorSpace (a -> v) where
--   type Scalar (a -> v) = Scalar v
--   (*^) s = fmap (s *^)

-- No 'InnerSpace' instance for @a -> v@.

-- Or the following definition, which is useful for the higher-order
-- shading dsel in Shady (borrowed from Vertigo).

instance VectorSpace v => VectorSpace (a -> v) where
  type Scalar (a -> v) = a -> Scalar v
  (*^) = liftA2 (*^)

instance InnerSpace v => InnerSpace (a -> v) where
  (<.>) = liftA2 (<.>)



instance (HasTrie a, VectorSpace v) => VectorSpace (a :->: v) where
  type Scalar (a :->: v) = Scalar v
  (*^) s = fmap (s *^)



instance InnerSpace a => InnerSpace (Maybe a) where
  -- dotting with zero (vector) yields zero (scalar)
  Nothing <.> _     = zeroV
  _ <.> Nothing     = zeroV
  Just u <.> Just v = u <.> v

--   mu <.> mv = fromMaybe zeroV (liftA2 (<.>) mu mv)

--   (<.>) = (fmap.fmap) (fromMaybe zeroV) (liftA2 (<.>))
