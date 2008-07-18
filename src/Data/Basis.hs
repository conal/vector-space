{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances
  , FlexibleInstances, MultiParamTypeClasses
  #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Basis
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Basis of a vector space, as an associated type
----------------------------------------------------------------------

module Data.Basis
  (
    HasBasis(..)
  ) where

import Control.Arrow (second)
import Data.Either

import Data.VectorSpace

class VectorSpace v s => HasBasis v s where
  type Basis v :: *
  basisValue :: Basis v -> v
  decompose :: v -> [(s, Basis v)]

-- TODO: switch from fundep to associated type.  eliminate the second type
-- parameter in VectorSpace and HasBasis.
-- Blocking bug: http://hackage.haskell.org/trac/ghc/ticket/2448

instance HasBasis Float Float where
  type Basis Float = ()
  basisValue ()    = 1
  decompose s      = [(s,())]

instance HasBasis Double Double where
  type Basis Double = ()
  basisValue ()     = 1
  decompose s       = [(s,())]

instance (HasBasis u s, HasBasis v s) => HasBasis (u,v) s where
  type Basis (u,v)     = Basis u `Either` Basis v
  basisValue (Left  a) = (basisValue a, zeroV)
  basisValue (Right b) = (zeroV, basisValue b)
  decompose (u,v)      = decomp2 Left u ++ decomp2 Right v

decomp2 :: HasBasis w s => (Basis w -> b) -> w -> [(s, b)]
decomp2 inject = fmap (second inject) . decompose

instance (HasBasis u s, HasBasis v s, HasBasis w s) => HasBasis (u,v,w) s where
  type Basis (u,v,w) = Basis (u,(v,w))
  basisValue         = unnest3 . basisValue
  decompose          = decompose . nest3

unnest3 :: (a,(b,c)) -> (a,b,c)
unnest3 (a,(b,c)) = (a,b,c)

nest3 :: (a,b,c) -> (a,(b,c))
nest3 (a,b,c) = (a,(b,c))

-- Without UndecidableInstances:
-- 
--     Application is no smaller than the instance head
--       in the type family application: Basis (u, (v, w))
--     (Use -fallow-undecidable-instances to permit this)
--     In the type synonym instance declaration for `Basis'
--     In the instance declaration for `HasBasis (u, v, w)'
-- 
-- A work-around:
-- 
--     type Basis (u,v,w) = Basis u `Either` Basis (v,w)


{-

---- Testing

t1 = basisValue () :: Float
t2 = basisValue () :: Double
t3 = basisValue (Right ()) :: (Float,Double)
t4 = basisValue (Right (Left ())) :: (Float,Double,Float)

-}

