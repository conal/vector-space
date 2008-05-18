{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies 
           , FlexibleInstances, FlexibleContexts, UndecidableInstances
 #-}
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
----------------------------------------------------------------------

module Data.VectorSpace
  ( 
    VectorSpace(..), (^-^), (^/), (^*)
  , InnerSpace(..) --, Scalar
  , lerp, magnitudeSq, magnitude, normalized
  , (:-*)
  ) where

import Control.Applicative

infixr 7 *^, ^/, <.>
infixl 7 ^*
infixl 6 ^+^, ^-^

-- | Vector space @v@ over a scalar field @s@
class VectorSpace v s | v -> s where
  -- | The zero vector
  zeroV :: v
  -- | Scale a vector
  (*^)  :: s -> v -> v
  -- | Add vectors
  (^+^) :: v -> v -> v
  -- | Additive inverse
  negateV :: v -> v

-- | Adds inner (dot) products
class VectorSpace v s => InnerSpace v s | v -> s where
  -- | Inner/dot product
  (<.>) :: v -> v -> s

-- | Convenience.  Maybe add methods later.
-- class VectorSpace s s => Scalar s

-- TODO: consider replacing v with a type constructor argument:
-- 
-- class VectorSpace v where
--   zeroV :: v s
--   (*^)  :: s -> v s -> v s
--   (^+^) :: v s -> v s -> v s
--   (<.>)   :: v s -> v s -> s
-- 
-- Perhaps with constraints on s.  We couldn't then define instances for
-- doubles & floats.

-- | Vector subtraction
(^-^) :: VectorSpace v s => v -> v -> v
v ^-^ v' = v ^+^ negateV v'

-- | Vector divided by scalar
(^/) :: (Fractional s, VectorSpace v s) => v -> s -> v
v ^/ s = (1/s) *^ v

-- | Vector multiplied by scalar
(^*) :: VectorSpace v s => v -> s -> v
(^*) = flip (*^)

-- | Linear interpolation between @a@ (when @t==0@) and @b@ (when @t==1@).
lerp :: (VectorSpace v s, Num s) => v -> v -> s -> v
lerp a b t = (1-t)*^a ^+^ t*^b

-- | Square of the length of a vector.  Sometimes useful for efficiency.
-- See also 'magnitude'.
magnitudeSq :: InnerSpace v s =>  v -> s
magnitudeSq v = v <.> v

-- | Length of a vector.   See also 'magnitudeSq'.
magnitude :: (InnerSpace v s, Floating s) =>  v -> s
magnitude = sqrt . magnitudeSq

-- | Vector in same direction as given one but with length of one.  If
-- given the zero vector, then return it.
normalized :: (InnerSpace v s, Floating s) =>  v -> v
normalized v | mag /= 0  = v ^/ mag
             | otherwise = v
  where
    mag = magnitude v

instance VectorSpace Double Double where
  zeroV   = 0.0
  (*^)    = (*)
  (^+^)   = (+)
  negateV = negate

instance InnerSpace Double Double where
 (<.>) = (*)

instance VectorSpace Float Float where
  zeroV   = 0.0
  (*^)    = (*)
  (^+^)   = (+)
  negateV = negate

instance InnerSpace Float Float where
  (<.>) = (*)

-- With UndecidableInstances, I get
--   Illegal instance declaration for `VectorSpace (u, v) s' (the
--   Coverage Condition fails for one of the functional dependencies ...)

instance (VectorSpace u s,VectorSpace v s) => VectorSpace (u,v) s where
  zeroV             = (zeroV,zeroV)
  s *^ (u,v)        = (s*^u,s*^v)
  (u,v) ^+^ (u',v') = (u^+^u',v^+^v')
  negateV (u,v)     = (negateV u, negateV v)

instance (InnerSpace u s,InnerSpace v s, VectorSpace s s')
    => InnerSpace (u,v) s where
  (u,v) <.> (u',v') = (u <.> u') ^+^ (v <.> v')

-- We could use @Num s@ and @(+)@ in place of @VectorSpace s s'@ and @(^+^)@
-- in the @InnerSpace@ instances for pairs and triples.

instance (VectorSpace u s,VectorSpace v s,VectorSpace w s)
    => VectorSpace (u,v,w) s where
  zeroV                  = (zeroV,zeroV,zeroV)
  s *^ (u,v,w)           = (s*^u,s*^v,s*^w)
  (u,v,w) ^+^ (u',v',w') = (u^+^u',v^+^v',w^+^w')
  negateV (u,v,w)        = (negateV u, negateV v, negateV w)

instance (InnerSpace u s,InnerSpace v s,InnerSpace w s, VectorSpace s s')
    => InnerSpace (u,v,w) s where
  (u,v,w) <.> (u',v',w') = u<.>u' ^+^ v<.>v' ^+^ w<.>w'


-- Standard instance for an applicative functor applied to a vector space.
instance VectorSpace v s => VectorSpace (a->v) s where
  zeroV   = pure   zeroV
  (*^) s  = fmap (s *^)
  (^+^)   = liftA2 (^+^)
  negateV = fmap negateV

-- I don't know how to make the InnerSpace class work out, because the
-- inner product would have to combine two vector *functions* into a
-- scalar value.
-- 
--   instance InnerSpace v s => InnerSpace (a->v) s where
--     (<.>) = ???

-- Alternatively, we could use (a->s) as the scalar field:
-- 
--   -- Standard instance for an applicative functor applied to a vector space.
--   instance VectorSpace v s => VectorSpace (a->v) (a->s) where
--     zeroV   = pure   zeroV
--     (*^)    = liftA2 (*^)
--     (^+^)   = liftA2 (^+^)
--     negateV = fmap negateV
-- 
--   instance InnerSpace v s => InnerSpace (a->v) (a->s) where
--     (<.>) = liftA2 (<.>)
-- 
-- This definition, however, doesn't fit the standard notion of linear
-- maps as vector spaces.


-- | Linear transformations/maps.  For now, represented as simple
-- functions.  The 'VectorSpace' instance for functions gives the usual
-- meaning for a vector space of linear transformations.

type a :-* b = a -> b
