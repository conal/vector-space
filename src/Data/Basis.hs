{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances #-}
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

module Data.Basis (HasBasis(..)) where

import Data.Either

import Data.AdditiveGroup
-- import Data.VectorSpace

class AdditiveGroup v => HasBasis v where
  type Basis v :: *
  basisValue :: Basis v -> v

instance HasBasis Float where
  type Basis Float = ()
  basisValue () = 1

instance HasBasis Double where
  type Basis Double = ()
  basisValue () = 1

instance (HasBasis u, HasBasis v) => HasBasis (u,v) where
  type Basis (u,v) = Basis u `Either` Basis v
  basisValue (Left  a) = (basisValue a, zeroV)
  basisValue (Right b) = (zeroV, basisValue b)

instance (HasBasis u, HasBasis v, HasBasis w) => HasBasis (u,v,w) where
  type Basis (u,v,w) = Basis (u,(v,w))
  basisValue = flat3 . basisValue
   where flat3 (a,(b,c)) = (a,b,c)

-- Without UndecidableInstances:
-- 
--     Application is no smaller than the instance head
--       in the type family application: Basis (u, (v, w))
--     (Use -fallow-undecidable-instances to permit this)
--     In the type synonym instance declaration for `Basis'
--     In the instance declaration for `HasBasis (u, v, w)'

-- Work-around:
-- 
--     type Basis (u,v,w) = Basis u `Either` Basis (v,w)



-- Testing

t1 = basisValue () :: Float
t2 = basisValue () :: Double
t3 = basisValue (Right ()) :: (Float,Double)
t4 = basisValue (Right (Left ())) :: (Float,Double,Float)
