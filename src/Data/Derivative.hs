{-# LANGUAGE TypeOperators, FlexibleInstances, MultiParamTypeClasses
           , UndecidableInstances
  #-}
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
    (:>)(..), (::>), dZero, dConst, dId, bilinearD, (>*<), (>-<)
  ) where

import Control.Applicative

import Data.VectorSpace
import Data.NumInstances ()


infixr 9 `D`

-- | Tower of derivatives.  Values look like @b `D` b' `D` b'' `D` ...@.
-- The type of an @n@th derivative is @a :-* a :-* ... :-* b@, where there
-- are @n@ levels of @a :-*@, i.e., @(a :-*)^n b@.
-- 
-- Warning, the 'Applicative' instance is missing its 'pure' (due to a
-- 'VectorSpace' type constraint).  Use 'dConst' instead.
data a :> b = D b (a :> (a :-* b))

-- | Infinitely differentiable functions
type a ::> b = a -> (a:>b)

instance Functor ((:>) a) where
  fmap f (D b b') = D (f b) (f `onDer` b')

-- I think fmap will be meaningful only with *linear* functions.

-- Lift a function to act on values inside of derivative towers
onDer :: (b -> c) -> (a :> (a :-* b)) -> (a :> (a :-* c))
onDer f = fmap (f .)

-- Or fmap.(.), or fmap.fmap

instance Applicative ((:>) a) where
    -- pure = dConst    -- not!  see below.
    pure = noOv "pure.  use dConst instead."
    D f f' <*> D b b' = D (f b) (liftA2 (<*>) f' b')

-- Why can't we define 'pure' as 'dConst'?  Because of the extra type
-- constraint that @VectorSpace b@ (not @a@).  Oh well.  Be careful not to
-- use 'pure', okay?  Alternatively, I could define the '(<*>)' (naming it
-- something else) and then say @foo <$> p <*^> q <*^> ...@.

-- | Derivative tower full of 'zeroV'.
dZero :: VectorSpace b s => a:>b
dZero = w where w = zeroV `D` dZero

-- | Constant derivative tower.
dConst :: VectorSpace b s => b -> a:>b
dConst b = b `D` dZero

-- | Tower of derivatives of the identity function.  Sometimes called "the
-- derivation variable" or similar, but it's not really a variable.
dId :: VectorSpace v s => v -> v:>v
dId v = w where w = v `D` dConst id

-- Derivative tower for applying a bilinear function, such as
-- multiplication.
bilinearD :: VectorSpace w s =>
             (u -> v -> w) -> (t :> u) -> (t :> v) -> (t :> w)
bilinearD op (D s s') (D u u') =
  D (s `op` u) ((s `op`) `onDer` u' ^+^ (`op` u) `onDer` s')


-- Handy for missing methods.
noOv :: String -> a
noOv op = error (op ++ ": not defined on a :> b")

-- I'm not sure about the next three, which discard information
instance Show b => Show (a :> b) where show    = noOv "show"
instance Eq   b => Eq   (a :> b) where (==)    = noOv "(==)"
instance Ord  b => Ord  (a :> b) where compare = noOv "compare"

instance VectorSpace u s => VectorSpace (a :> u) (a :> s) where
  zeroV   = dConst    zeroV    -- or dZero
  (*^)    = bilinearD (*^)
  negateV = fmap      negateV
  (^+^)   = liftA2    (^+^)


infix 0 >*<

-- | Convenient encapsulation of the chain rule.  Combines value function
-- and derivative function, to get a infinitely differentiability
-- function, which is then applied to a derivative tower.
(>*<) :: (b -> c) -> (b -> (b :-* c))
      -> (a :> b) -> (a :> c)
f >*< f' = \ (D u u') -> D (f u) ((f' u .) <$> u')

-- Compare with:
-- 
--   f >-< f' = \ (D u u') -> D (f u) (f' u *^ u')
-- 
-- which is equivalent to
-- 
--   f >-< f' = \ (D u u') -> D (f u) ((f' u *^) <$> u')
-- 
-- thanks to the 'VectorSpace' instance of @a :> b@

-- Also, we could have said
-- 
--   f >*< f' = \ (D u u') -> D (f u) ((fmap.fmap) (f' u) u')
-- 
-- because (.) and (<$>) are both 'fmap'.


-- Specialized chain rule.  Scalar range.
infix 0 >-<
-- | Specialized form of '(>*<)', convenient for functions with scalar
-- values.  Uses the more common view of derivatives as rate-of-change.
(>-<) :: VectorSpace b s => (b -> b) -> (b -> s)
      -> (a :> b) -> (a :> b)
f >-< f' = f >*< ((*^) . f')

-- Equivalently:
-- 
--   f >-< f' = f >:< \ u -> (f' u *^)
-- or
--            = \ (D u u') -> D (f u) (f' u *^ u')
-- 
-- Corresponding to the usual chain rule for scalar domains:
--   D (f . g) x = D f (g x) *^ D g x


-- Note that the two arguments of (>*<) have the same info as @a ::> b@.
-- Define composition functions as I did in DifL.


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




-- infixl 9 @$
-- -- Application, with chain rule
-- (@$) :: b ::> c -> a :> b -> a :> c
-- g @$ u = D c ((fmap.fmap) c' b')
--  where
--    D b b' = u
--    D c c' = g b

-- b  :: b
-- b' :: a :> (a :-* b)

-- c  :: c
-- c' :: b :> (b :-* c)

-- b  = f x
-- b' = D f x

-- c  = g (f x)
-- c' = D g (f x)


-- D (g . f) x = D g (f x) . D f x
--  == c' . b'




-- g @$ D b b' = D c (c' . b')
--  where
--    D c c' = g b


-- -- Composition, with chain rule
-- infixr 9 @.
-- (@.) :: b ::> c -> a ::> b -> a ::> c
-- (g @. f) a = g @$ f a

-- (g @. f) a = D c (c' . b')
--  where
--    D b b' = f a
--    D c c' = g b
