{-# LANGUAGE TypeOperators, MultiParamTypeClasses, UndecidableInstances
           , TypeSynonymInstances, FlexibleInstances, FunctionalDependencies
           , FlexibleContexts
  #-}

-- TODO: remove FlexibleContexts

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
    (:>), powVal, derivative, derivativeAt
  , (:~>), dZero, pureD
  , fmapD, (<$>>){-, (<*>>)-}, liftD2, liftD3
  , idD, fstD, sndD
  , linearD, distrib
  , (@.), (>-<)
  ,(**^), (<*.>)
  -- , HasDeriv(..)
  -- experimental
  -- , liftD3
  ) where

-- import Control.Applicative

import Data.VectorSpace
import Data.NumInstances ()
import Data.LinearMap


infixr 9 `D`, @.
infixl 4 {-<*>>,-} <$>>
infix  0 >-<


-- | Tower of derivatives.
data a :> b = D { powVal :: b, derivative :: a :-* (a :> b) }

-- | Infinitely differentiable functions
type a :~> b = a -> (a:>b)

-- | Sampled derivative.  For avoiding an awkward typing problem related
-- to the two required 'VectorSpace' instances.
derivativeAt :: (VectorSpace b s, LMapDom a s) =>
                (a :> b) -> a -> (a :> b)
derivativeAt d = ($*) (derivative d)

-- The crucial point here is for '($*)' to be interpreted with respect to
-- the 'VectorSpace' instance in this module, not Mac.

-- The argument order for 'derivativeAt' allows partial evaluation, which
-- is useful in power series representations for which 'derivative' is not
-- free (Horner).

-- Handy for missing methods.
noOv :: String -> a
noOv op = error (op ++ ": not defined on a :> b")

-- | Derivative tower full of 'zeroV'.
dZero :: (LMapDom a s, AdditiveGroup b) => a:>b
dZero = pureD zeroV

-- | Constant derivative tower.
pureD :: (LMapDom a s, AdditiveGroup b) => b -> a:>b
pureD b = b `D` pureL dZero

-- | Map a /linear/ function over a derivative tower.
fmapD, (<$>>) :: (LMapDom a s, VectorSpace b s) =>
                 (b -> c) -> (a :> b) -> (a :> c)
fmapD f (D b0 b') = D (f b0) ((fmapL.fmapD) f b')

(<$>>) = fmapD

-- -- | Like '(<*>)' for derivative towers.
-- (<*>>) :: (LMapDom a s, VectorSpace b s, VectorSpace c s) =>
--           (a :> (b -> c)) -> (a :> b) -> (a :> c)
-- D f0 f' <*>> D x0 x' = D (f0 x0) (liftL2 (<*>>) f' x')

-- | Apply a /linear/ binary function over derivative towers.
liftD2 :: (VectorSpace b s, LMapDom a s, VectorSpace c s, VectorSpace d s) =>
          (b -> c -> d) -> (a :> b) -> (a :> c) -> (a :> d)
liftD2 f (D b0 b') (D c0 c') = D (f b0 c0) (liftL2 (liftD2 f) b' c')

-- | Apply a /linear/ ternary function over derivative towers.
liftD3 :: ( LMapDom a s
          , VectorSpace b s, VectorSpace c s
          , VectorSpace d s, VectorSpace e s ) =>
          (b -> c -> d -> e)
       -> (a :> b) -> (a :> c) -> (a :> d) -> (a :> e)
liftD3 f (D b0 b') (D c0 c') (D d0 d') = D (f b0 c0 d0) (liftL3 (liftD3 f) b' c' d')

-- | Differentiable identity function.  Sometimes called "the
-- derivation variable" or similar, but it's not really a variable.
idD :: (LMapDom u s, VectorSpace u s) => u :~> u
idD = linearD id

-- or
--   dId v = D v pureD

-- | Every linear function has a constant derivative equal to the function
-- itself (as a linear map).
linearD :: (LMapDom u s, VectorSpace v s) => (u -> v) -> (u :~> v)
linearD f u = D (f u) (linear (pureD . f))

-- Other examples of linear functions

-- | Differentiable version of 'fst'
fstD :: (VectorSpace a s, LMapDom b s, LMapDom a s) => (a,b) :~> a
fstD = linearD fst

-- | Differentiable version of 'snd'
sndD :: (VectorSpace b s, LMapDom b s, LMapDom a s) => (a,b) :~> b
sndD = linearD snd

-- | Derivative tower for applying a binary function that distributes over
-- addition, such as multiplication.  A bit weaker assumption than
-- bilinearity.
distrib :: (LMapDom a s, VectorSpace b s, VectorSpace c s, VectorSpace u s) =>
           (b -> c -> u) -> (a :> b) -> (a :> c) -> (a :> u)
distrib op = opD
 where
   opD u@(D u0 u') v@(D v0 v') =
     D (u0 `op` v0) (linear (\ da -> u `opD` (v' $* da) ^+^ (u' $* da) `opD` v))

-- Equivalently:
-- 
--    opD u@(D u0 u') v@(D v0 v') =
--      D (u0 `op` v0) (linear ((u `opD`) . ($*) v' ^+^ (`opD` v) . ($*) u'))



-- TODO: look for a simpler definition of distrib.  this definition almost
-- fits liftLM2.


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

-- ouch!  InnerSpace one won't work at all, for the same reason as for functions.
                  
-- instance (InnerSpace u s) => InnerSpace (a :> u) s where
--   (<.>) = distrib (<.>)

(<*.>) :: (LMapDom a s, InnerSpace b s, VectorSpace s s) =>
          (a :> b) -> (a :> b) -> (a :> s)
(<*.>) s = distrib (<.>) s


-- The instances below are the one I think we'll want externally.
-- However, the ones above allow the definition of @a:>b@ to work out.
-- The module "Data.Mac" rewraps to provide the alternate instances.

-- instance (LMapDom a s, VectorSpace u s, VectorSpace s s)
--     => VectorSpace (a :> u) (a :> s) where
--   (*^) = (**^)

-- instance (InnerSpace u s, InnerSpace s s', VectorSpace s s, LMapDom a s) =>
--      InnerSpace (a :> u) (a :> s) where
--   (<.>) = (<*.>)


-- | Chain rule.  See also '(>-<)'.
(@.) :: (LMapDom b s, LMapDom a s, VectorSpace c s) =>
        (b :~> c) -> (a :~> b) -> (a :~> c)
(h @. g) a0 = D c0 (inL2 (@.) c' b')
  where
    D b0 b' = g a0
    D c0 c' = h b0

-- | Specialized chain rule.  See also '(@.)'.
(>-<) :: (LMapDom a s, VectorSpace s s, VectorSpace u s) =>
         (u -> u) -> ((a :> u) -> (a :> s))
      -> (a :> u) -> (a :> u)
f >-< f' = \ u@(D u0 u') -> D (f u0) ((f' u **^) <$>* u')

-- TODO: express '(>-<)' in terms of '(@.)'.  If I can't, then understand why not.

instance (LMapDom a b, Num b, VectorSpace b b) => Num (a:>b) where
  fromInteger = pureD . fromInteger
  (+) = liftD2  (+)
  (-) = liftD2  (-)
  (*) = distrib (*)
  negate = negate >-< -1
  abs    = abs    >-< signum
  signum = signum >-< 0  -- derivative wrong at zero

instance (LMapDom a b, Fractional b, VectorSpace b b) => Fractional (a:>b) where
  fromRational = pureD . fromRational
  recip        = recip >-< recip sqr

sqr :: Num a => a -> a
sqr x = x*x

instance (LMapDom a b, Floating b, VectorSpace b b) => Floating (a:>b) where
  pi    = pureD pi
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
