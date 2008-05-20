{-# LANGUAGE TypeOperators, MultiParamTypeClasses, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Derivative
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Infinite derivative towers via linear maps.  See blog posts
-- <http://conal.net/blog/tag/derivatives/>
----------------------------------------------------------------------

module Data.Derivative
  (
    (:>)(..), (:~>), dZero, dConst, dId
  , linearD, bilinearD
  , (@.), (>-<)
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
data a :> b = D { dVal :: b, dDeriv :: a :-* (a :> b) }

-- data a :> b = D b (a :-* (a :> b))

-- | Infinitely differentiable functions
type a :~> b = a -> (a:>b)

-- So we could define
-- 
--   data a :> b = D b (a :~> b)
-- 
-- with the restriction that the a :~> b is linear

instance Functor ((:>) a) where
  fmap f (D b b') = D (f b) (f `onDer` b')

-- I think fmap will be meaningful only with *linear* functions.

-- Lift a function to act on values inside of derivative towers
onDer :: (b -> c) -> (a :~> b) -> (a :~> c)
onDer = fmap.fmap

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

-- | Constant derivative tower.
dConst :: VectorSpace b s => b -> a:>b
dConst b = b `D` const dZero

-- | Derivative tower full of 'zeroV'.
dZero :: VectorSpace b s => a:>b
dZero = dConst zeroV

-- | Tower of derivatives of the identity function.  Sometimes called "the
-- derivation variable" or similar, but it's not really a variable.
dId :: VectorSpace v s => v -> v:>v
dId = linearD id

-- or
--   dId v = D v dConst

-- | Every linear function has a constant derivative equal to the function
-- itself (as a linear map).
linearD :: VectorSpace v s => (u :-* v) -> (u :~> v)
linearD f u = D (f u) (dConst . f)

-- | Derivative tower for applying a bilinear function, such as
-- multiplication.
bilinearD :: VectorSpace w s =>
             (u -> v -> w) -> (t :> u) -> (t :> v) -> (t :> w)
bilinearD op (D s s') (D u u') =
  D (s `op` u) ((s `op`) `onDer` u' ^+^ (`op` u) `onDer` s')

-- I'm not sure about the next three, which discard information
instance Show b => Show (a :> b) where show    = noOv "show"
instance Eq   b => Eq   (a :> b) where (==)    = noOv "(==)"
instance Ord  b => Ord  (a :> b) where compare = noOv "compare"

instance VectorSpace u s => VectorSpace (a :> u) (a :> s) where
  zeroV   = dConst    zeroV    -- or dZero
  (*^)    = bilinearD (*^)
  negateV = fmap      negateV
  (^+^)   = liftA2    (^+^)

-- | Chain rule.
(@.) :: (b :~> c) -> (a :~> b) -> (a :~> c)
(h @. g) a0 = D c0 (c' @. b')
  where
    D b0 b' = g a0
    D c0 c' = h b0


-- | Specialized chain rule.
(>-<) :: VectorSpace b s => (b -> b) -> ((a :> b) -> (a :> s))
      -> (a :> b) -> (a :> b)
f >-< f' = \ b@(D b0 b') -> D (f b0) ((f' b *^) . b')


instance (Num b, VectorSpace b b) => Num (a:>b) where
  fromInteger = dConst . fromInteger
  (+) = liftA2    (+)
  (-) = liftA2    (-)
  (*) = bilinearD (*)
  
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
