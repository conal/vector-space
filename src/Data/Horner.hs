{-# LANGUAGE TypeOperators, MultiParamTypeClasses
           , TypeSynonymInstances, FlexibleInstances  #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Horner
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Infinite derivative towers via linear maps, using the Horner
-- representation.  See blog posts <http://conal.net/blog/tag/derivative/>.
----------------------------------------------------------------------

module Data.Horner
  (
    (:>), powVal, derivative, integral
  , (:~>), dZero, dConst
  , idD, fstD, sndD
  , linearD, distrib
  , (@.), (>-<)
  -- , HasDeriv(..)
  )
  where

import Control.Applicative

import Data.VectorSpace
import Data.LinearMap
import Data.NumInstances ()

infixr 9 `H`, @.
infix  0 >-<

-- | Power series
-- 
-- Warning, the 'Applicative' instance is missing its 'pure' (due to a
-- 'VectorSpace' type constraint).  Use 'dConst' instead.
data a :> b = H b (a :-* (a :> b))

-- | The plain-old (0th order) value
powVal :: (a :> b) -> b
powVal (H b _) = b

-- Apply successive functions to successive values
apPow :: [b -> c] -> (a :> b) -> (a :> c)
apPow [] _ = error "apPow: finite function list"
apPow (f : fs) (b0 `H` bt) = H (f b0) (apPow fs . bt)

-- Count.  Avoids the 'Enum' requirement of [1..]
from :: Num s => s -> [s]
from n = n : from (n+1) 

-- | Derivative of a power series
derivative :: (VectorSpace b s, Num s) =>
         (a :> b) -> (a :-* (a :> b))
derivative (H _ bt) = apPow ((*^) <$> from 1) . bt

-- | Integral of a power series
integral :: (VectorSpace b s, Fractional s) =>
            b -> (a :-* (a :> b)) -> (a :> b)
integral b0 bt = H b0 (apPow (((*^).recip) <$> from 1) . bt)

-- | Infinitely differentiable functions
type a :~> b = a -> (a:>b)

-- So we could define
-- 
--   data a :> b = H b (a :~> b)
-- 
-- with the restriction that the a :~> b is linear

instance Functor ((:>) a) where
  fmap f (H b b') = H (f b) ((fmap.fmap) f b')

-- I think fmap will be meaningful only with *linear* functions.

-- Handy for missing methods.
noOv :: String -> a
noOv op = error (op ++ ": not defined on a :> b")

instance Applicative ((:>) a) where
  -- pure = dConst    -- not!  see below.
  pure = noOv "pure"  -- use dConst instead
  H f f' <*> H b b' = H (f b) (liftA2 (<*>) f' b')

-- Why can't we define 'pure' as 'dConst'?  Because of the extra type
-- constraint that @VectorSpace b@ (not @a@).  Oh well.  Be careful not to
-- use 'pure', okay?  Alternatively, I could define the '(<*>)' (naming it
-- something else) and then say @foo <$> p <*^> q <*^> ...@.

-- | Constant derivative tower.
dConst :: VectorSpace b s => b -> a:>b
dConst b = b `H` const dZero

-- | Derivative tower full of 'zeroV'.
dZero :: VectorSpace b s => a:>b
dZero = dConst zeroV

-- | Differentiable identity function.  Sometimes called "the
-- derivation variable" or similar, but it's not really a variable.
idD :: VectorSpace u s => u :~> u
idD = linearD id

-- or
--   dId v = H v dConst

-- | Every linear function has a constant derivative equal to the function
-- itself (as a linear map).
linearD :: VectorSpace v s => (u :-* v) -> (u :~> v)
linearD f u = H (f u) (dConst . f)


-- Other examples of linear functions

-- | Differentiable version of 'fst'
fstD :: VectorSpace a s => (a,b) :~> a
fstD = linearD fst

-- | Differentiable version of 'snd'
sndD :: VectorSpace b s => (a,b) :~> b
sndD = linearD snd

-- | Derivative tower for applying a binary function that distributes over
-- addition, such as multiplication.  A bit weaker assumption than
-- bilinearity.
distrib :: (VectorSpace u s) =>
           (b -> c -> u) -> (a :> b) -> (a :> c) -> (a :> u)
distrib op = opD
 where
   opD (H u0 ut) v@(H v0 vt) =
     H (u0 `op` v0) (fmap (u0 `op`) . vt ^+^ (`opD` v) . ut)


-- Equivalently,
-- 
--   distrib op = opD
--    where
--      opD u@(H u0 u') v@(H v0 v') =
--        H (u0 `op` v0) (\ da -> ((u0 `op`) <$> v' da) ^+^ (u' da `opD` v))



-- I'm not sure about the next three, which discard information

instance Show b => Show (a :> b) where show    = noOv "show"
instance Eq   b => Eq   (a :> b) where (==)    = noOv "(==)"
instance Ord  b => Ord  (a :> b) where compare = noOv "compare"

instance (LMapDom a s, VectorSpace u s) => AdditiveGroup (a :> u) where
  zeroV   = pureD  zeroV    -- or dZero
  negateV = fmapD  negateV
  (^+^)   = liftD2 (^+^)

instance (LMapDom a s, VectorSpace u s) => VectorSpace (a :> u) s where
  (*^) s = fmapD  ((*^) s)

(**^) :: (VectorSpace c s, VectorSpace s s, LMapDom a s) =>
         (a :> s) -> (a :> c) -> (a :> c)
(**^) = distrib (*^)

-- | Chain rule.
(@.) :: (VectorSpace b s, VectorSpace c s, Num s) =>
        (b :~> c) -> (a :~> b) -> (a :~> c)
(h @. g) a0 = H c0 (derivative c @. derivative b)
  where
    b@(H b0 _) = g a0
    c@(H c0 _) = h b0


-- | Specialized chain rule.
(>-<) :: (VectorSpace u s, Fractional s) => (u -> u) -> ((a :> u) -> (a :> s))
      -> (a :> u) -> (a :> u)

-- f >-< f' = \ u@(D u0 u') -> D (f u0) ((f' u *^) . u')

f >-< f' = \ u@(H u0 _) -> integral (f u0) ((f' u *^) . derivative u)

-- TODO: consider eliminating @Num s@.  I just need a multiplicative unit.

-- Equivalently:
-- 
--   f >-< f' = \ u@(H u0 u') -> H (f u0) (\ da -> f' u *^ u' da)

instance (Fractional b, VectorSpace b b) => Num (a:>b) where
  fromInteger = dConst . fromInteger
  (+) = liftA2  (+)
  (-) = liftA2  (-)
  (*) = distrib (*)
  
  negate = negate >-< -1
  abs    = abs    >-< signum
  signum = signum >-< 0  -- derivative wrong at zero

instance (Fractional b, VectorSpace b b) => Fractional (a:>b) where
  fromRational = dConst . fromRational
  recip        = recip >-< recip sqr

sqr :: Num a => a -> a
sqr x = x*x

instance (Floating b, VectorSpace b b) => Floating (a:>b) where
  pi    = dConst pi
  exp   = exp   >-< exp
  log   = log   >-< recip
  sqrt  = sqrt  >-< recip (2 * sqrt)
  sin   = sin   >-< cos
  cos   = cos   >-< - sin
  sinh  = sinh  >-< cosh
  cosh  = cosh  >-< sinh
  asin  = asin  >-< recip (sqrt (1-sqr))
  acos  = acos  >-< recip (- sqrt (1-sqr))
  atan  = atan  >-< recip (1+sqr)
  asinh = asinh >-< recip (sqrt (1+sqr))
  acosh = acosh >-< recip (- sqrt (sqr-1))
  atanh = atanh >-< recip (1-sqr)

