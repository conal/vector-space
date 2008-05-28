{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances
           , MultiParamTypeClasses, FlexibleInstances
  #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.LinearMap
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Linear maps
----------------------------------------------------------------------

module Data.LinearMap
  (
    LMapDom(..), linearK, (.*)
  , fmapLM, liftLM2, liftLM3
  ) where

import Control.Applicative
import Data.Function

import Data.VectorSpace -- hiding ((:-*))


infixr 9 .*

-- | Domain of a linear map.
class VectorSpace a s => LMapDom a s where
  -- | Linear map type
  data (:-*) a :: * -> *
  -- | Linear map as function
  lapply :: VectorSpace b s => (a :-* b) -> (a -> b)
  -- | Function (assumed linear) as linear map.
  linear :: (a -> b) -> (a :-* b)

-- Map a /linear/ function over a linear map.
fmapLM :: (LMapDom a s, VectorSpace b s) =>
          (b -> c) -> (a :-* b) -> (a :-* c)
fmapLM f lm = linear (f . lapply lm)

liftLM2 :: (LMapDom a s, VectorSpace b s, VectorSpace c s) =>
           (b -> c -> d) -> (a :-* b) -> (a :-* c) -> (a :-* d)
liftLM2 f b c = linear (liftA2 f (lapply b) (lapply c))

liftLM3 :: (LMapDom a s, VectorSpace b s, VectorSpace c s, VectorSpace d s) =>
           (b -> c -> d -> e)
        -> (a :-* b) -> (a :-* c) -> (a :-* d) -> (a :-* e)
liftLM3 f b c d = linear (liftA3 f (lapply b) (lapply c) (lapply d))

-- | Constant value as a linear map
pureLM :: LMapDom a s => b -> (a :-* b)
pureLM b = linear (const b)

-- | Like '(<*>)' for linear maps
apLM :: (LMapDom a s, VectorSpace b s, VectorSpace c s) =>
        (a :-* (b -> c)) -> (a :-* b) -> (a :-* c)
apLM g f = linear (lapply g <*> lapply f)


-- | Compose linear maps
(.*) :: (VectorSpace c s, LMapDom b s, LMapDom a s) =>
        (b :-* c) -> (a :-* b) -> (a :-* c)
g .* f = linear (lapply g . lapply f)


-- Experimental 'VectorSpace' instance.
instance (VectorSpace v s, LMapDom u s) => VectorSpace (u :-* v) s where
  zeroV      = linear (const zeroV)
  s *^ lm    = linear ((s *^) . lapply lm)
  l ^+^ m    = linear (lapply l ^+^ lapply m)
  negateV lm = linear (negateV (lapply lm))

-- Alternatively, add some methods to 'LMapDom' and use them as follows:

-- -- Linear maps form a vector space
-- instance (VectorSpace o s, LinearMap a o s) => VectorSpace (a :--> o) s where
--   zeroV = zeroLM
--   (^+^) = addLM
--   (*^)  = scaleLM



--- Instances of LMapDom


instance LMapDom Float Float where
  data Float :-* v   = FloatLM v
  lapply (FloatLM v) = (*^ v)
  linear f           = FloatLM (f 1)

instance LMapDom Double Double where
  data Double :-* v   = DoubleLM v
  lapply (DoubleLM v) = (*^ v)
  linear f            = DoubleLM (f 1)


-- | Convenience function for 'linear' definitions.  Both functions are
-- assumed linear.
linearK :: (LMapDom a s) => (a -> b) -> (b -> c) -> a :-* c
linearK k f = linear (f . k)

instance (LMapDom a s, LMapDom b s) => LMapDom (a,b) s where
  data (a,b) :-* o = PairLM (a :-* o) (b :-* o)
  PairLM ao bo `lapply` (a,b) = ao `lapply` a ^+^ bo `lapply` b
  linear = liftA2 PairLM
             (linearK (\ a -> (a,zeroV)))
             (linearK (\ b -> (zeroV,b)))

-- Equivalently:
-- 
--   linear f =
--     PairLM (linear (f . (`pair` zeroV))) (linear (f . (zeroV `pair`)))

instance (LMapDom a s, LMapDom b s, LMapDom c s) => LMapDom (a,b,c) s where
  data (a,b,c) :-* o = TripleLM (a :-* o) (b :-* o) (c :-* o)
  TripleLM ao bo co `lapply` (a,b,c) =
    ao `lapply` a ^+^ bo `lapply` b ^+^ co `lapply` c
  linear = liftA3 TripleLM
             (linearK (\ a -> (a,zeroV,zeroV)))
             (linearK (\ b -> (zeroV,b,zeroV)))
             (linearK (\ c -> (zeroV,zeroV,c)))


