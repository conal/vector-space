{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies 
           , TypeOperators, FlexibleInstances, UndecidableInstances
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

-- NB: I'm attempting to replace fundeps with associated types.  See
-- NewVectorSpace.hs.  Ran into trouble with type equality constraints not
-- getting propagated.  Manuel Ch is looking into it.
-- 
-- Blocking bug: http://hackage.haskell.org/trac/ghc/ticket/2448

module Data.VectorSpace
  ( 
    module Data.AdditiveGroup
  , VectorSpace(..), (^/), (^*)
  , InnerSpace(..)
  , lerp, magnitudeSq, magnitude, normalized
  ) where

import Data.Complex hiding (magnitude)

import Data.AdditiveGroup
import Data.MemoTrie

infixr 7 *^, ^/, <.>
infixl 7 ^*

-- | Vector space @v@ over a scalar field @s@.  Extends 'AdditiveGroup'
-- with scalar multiplication.
class AdditiveGroup v => VectorSpace v s | v -> s where
  -- | Scale a vector
  (*^)  :: s -> v -> v

-- | Adds inner (dot) products.
class VectorSpace v s => InnerSpace v s where
  -- | Inner/dot product
  (<.>) :: v -> v -> s

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
magnitudeSq :: InnerSpace v s => v -> s
magnitudeSq v = v <.> v

-- | Length of a vector.   See also 'magnitudeSq'.
magnitude :: (InnerSpace v s, Floating s) =>  v -> s
magnitude = sqrt . magnitudeSq

-- | Vector in same direction as given one but with length of one.  If
-- given the zero vector, then return it.
normalized :: (InnerSpace v s, Floating s) =>  v -> v
normalized v = v ^/ magnitude v

instance VectorSpace Double Double where (*^)  = (*)
instance InnerSpace  Double Double where (<.>) = (*)

instance VectorSpace Float  Float  where (*^)  = (*)
instance InnerSpace  Float  Float  where (<.>) = (*)

instance (RealFloat v, VectorSpace v s) => VectorSpace (Complex v) s where
  s*^(u :+ v) = s*^u :+ s*^v

instance (RealFloat v, InnerSpace v s, AdditiveGroup s)
     => InnerSpace (Complex v) s where
  (u :+ v) <.> (u' :+ v') = (u <.> u') ^+^ (v <.> v')

-- Hm.  The 'RealFloat' constraint is unfortunate here.  It's due to a
-- questionable decision to place 'RealFloat' into the definition of the
-- 'Complex' /type/, rather than in functions and instances as needed.

instance (VectorSpace u s,VectorSpace v s) => VectorSpace (u,v) s where
  s *^ (u,v) = (s*^u,s*^v)

instance (InnerSpace u s,InnerSpace v s, AdditiveGroup s)
    => InnerSpace (u,v) s where
  (u,v) <.> (u',v') = (u <.> u') ^+^ (v <.> v')

instance (VectorSpace u s,VectorSpace v s,VectorSpace w s)
    => VectorSpace (u,v,w) s where
  s *^ (u,v,w) = (s*^u,s*^v,s*^w)

instance (InnerSpace u s,InnerSpace v s,InnerSpace w s, AdditiveGroup s)
    => InnerSpace (u,v,w) s where
  (u,v,w) <.> (u',v',w') = u<.>u' ^+^ v<.>v' ^+^ w<.>w'


-- Standard instance for an applicative functor applied to a vector space.
instance VectorSpace v s => VectorSpace (a->v) s where
  (*^) s = fmap (s *^)

-- No 'InnerSpace' instance for @(a->v)@.

instance (HasTrie u, VectorSpace v s, AdditiveGroup (u :->: v))
         => VectorSpace (u :->: v) s where
  (*^) s = fmap (s *^)

-- The 'AdditiveGroup' constraint is implied by the others, thanks to the
-- instance in Data.AdditiveGroup.  Why isn't ghc figuring it out?
