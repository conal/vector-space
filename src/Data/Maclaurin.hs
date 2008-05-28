{-# LANGUAGE TypeOperators, MultiParamTypeClasses, UndecidableInstances
           , TypeSynonymInstances, FlexibleInstances, FunctionalDependencies
  #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Maclaurin
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Infinite derivative towers via linear maps, using the Maclaurin
-- representation.  See blog posts <http://conal.net/blog/tag/derivatives/>.
----------------------------------------------------------------------

module Data.Maclaurin
  (
    (:>), powVal, derivative
  , (:~>), dZero, dConst
  , idD, fstD, sndD
  , linearD, distrib
  , (@.), (>-<)
  -- , HasDeriv(..)
  -- experimental
  -- , liftD3
  ) where

import Control.Applicative

import Data.VectorSpace
import Data.NumInstances ()


infixr 9 `D`, @.
infix  0 >-<


-- | Tower of derivatives.
-- 
-- Warning, the 'Applicative' instance is missing its 'pure' (due to a
-- 'VectorSpace' type constraint).  Use 'dConst' instead.
data a :> b = D { powVal :: b, derivative :: a :-* (a :> b) }

-- | Infinitely differentiable functions
type a :~> b = a -> (a:>b)

-- So we could define
-- 
--   data a :> b = D b (a :~> b)
-- 
-- with the restriction that the a :~> b is linear

instance Functor ((:>) a) where
  fmap f (D b0 b') = D (f b0) ((fmap.fmap) f b')

-- I think fmap will be meaningful only with *linear* functions.

-- Handy for missing methods.
noOv :: String -> a
noOv op = error (op ++ ": not defined on a :> b")

instance Applicative ((:>) a) where
  -- pure = dConst    -- not!  see below.
  pure = noOv "pure.  use dConst instead."
  D f f' <*> D b b' = D (f b) (liftA2 (<*>) f' b')

-- Why can't we define 'pure' as 'dConst'?  Because of the extra type
-- constraint that @VectorSpace b@ (not @a@).  Oh well.  Be careful not to
-- use 'pure', okay?  Alternatively, I could define the '(<*>)' (naming it
-- something else) and then say @foo <$> p <*^> q <*^> ...@.


-- -- experimental
-- liftD3 :: (b -> c -> d -> e)
--        -> (a :> b) -> (a :> c) -> (a :> d) -> (a :> e)
-- liftD3 f (D b0 b') (D c0 c') (D d0 d') =
--   D (f b0 c0 d0) (liftA3 (liftD3 f) b' c' d')


-- | Constant derivative tower.
dConst :: VectorSpace b s => b -> a:>b
dConst b = b `D` const dZero

-- | Derivative tower full of 'zeroV'.
dZero :: VectorSpace b s => a:>b
dZero = dConst zeroV

-- | Differentiable identity function.  Sometimes called "the
-- derivation variable" or similar, but it's not really a variable.
idD :: VectorSpace u s => u :~> u
idD = linearD id

-- or
--   dId v = D v dConst

-- | Every linear function has a constant derivative equal to the function
-- itself (as a linear map).
linearD :: VectorSpace v s => (u :-* v) -> (u :~> v)
linearD f u = D (f u) (dConst . f)


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
   opD u@(D u0 u') v@(D v0 v') =
     D (u0 `op` v0) ((u `opD`) . v' ^+^ (`opD` v) . u')

-- Equivalently,
-- 
--   distribD op = opD
--    where
--      opD u@(D u0 u') v@(D v0 v') =
--        D (u0 `op` v0) (\ da -> (u `opD` v' da) ^+^ (u' da `opD` v))


-- I'm not sure about the next three, which discard information

instance Show b => Show (a :> b) where show    = noOv "show"
instance Eq   b => Eq   (a :> b) where (==)    = noOv "(==)"
instance Ord  b => Ord  (a :> b) where compare = noOv "compare"

instance VectorSpace u s => VectorSpace (a :> u) (a :> s) where
  zeroV   = dConst  zeroV    -- or dZero
  (*^)    = distrib (*^)
  negateV = fmap    negateV
  (^+^)   = liftA2  (^+^)

instance (InnerSpace u s, InnerSpace s s') =>
     InnerSpace (a :> u) (a :> s) where
  (<.>) = distrib (<.>)

-- | Chain rule.
(@.) :: (b :~> c) -> (a :~> b) -> (a :~> c)
(h @. g) a0 = D c0 (c' @. b')
  where
    D b0 b' = g a0
    D c0 c' = h b0


-- | Specialized chain rule.
(>-<) :: VectorSpace u s => (u -> u) -> ((a :> u) -> (a :> s))
      -> (a :> u) -> (a :> u)

f >-< f' = \ u@(D u0 u') -> D (f u0) ((f' u *^) . u')

-- Equivalently:
-- 
--   f >-< f' = \ u@(D u0 u') -> D (f u0) (\ da -> f' u *^ u' da)

instance (Num b, VectorSpace b b) => Num (a:>b) where
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


----

-- -- | Things with derivatives.
-- class HasDeriv a d | a -> d where deriv :: a -> d

-- instance HasDeriv (a:>b) (a :-* (a :> b)) where deriv = dDeriv

-- -- Standard instance for any functor
-- instance HasDeriv a d => HasDeriv (x -> a) (x -> d) where
--   deriv = fmap deriv

-- This code compiles fine, but I'm don't know whether it's worth it
