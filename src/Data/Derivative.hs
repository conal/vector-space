{-# LANGUAGE TypeOperators, MultiParamTypeClasses, UndecidableInstances
           , TypeSynonymInstances, FlexibleInstances, FunctionalDependencies
           , FlexibleContexts
           , GeneralizedNewtypeDeriving, StandaloneDeriving
  #-}

-- TODO: remove FlexibleContexts

-- {-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.Derivative
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- This module is a wrapper around Data.Maclaurin or Data.Horner, to
-- change the 'VectorSpace' instance for '(:>)'.
----------------------------------------------------------------------

module Data.Derivative
  (
    (:>), powVal, derivative, derivativeAt
  , (:~>), dZero, pureD
  , fmapD, (<$>>){-, (<*>>)-}, liftD2, liftD3
  , idD, fstD, sndD
  , linearD, distrib
  , (@.), (>-<)
  ) where

import Data.Function (on)

import Data.VectorSpace
import Data.NumInstances ()
import Data.LinearMap

import qualified Data.Maclaurin as D
-- import qualified Data.Horner as D

-- TODO: sync Data.Horner interface with Data.Maclaurin.  Better: refactor
-- Maclaurin into a module that depends on the representation (e.g.,
-- Horner vs Maclaurin) and the rest that doesn't.

infixr 9 @.
infixl 4 {-<*>>,-} <$>>
infix  0 >-<


-- | Tower of derivatives.
newtype (a :> b) = T { unT :: a D.:> b }

deriving instance (VectorSpace b b, LMapDom a b, Num b       ) => Num           (a :> b)
deriving instance (VectorSpace b b, LMapDom a b, Fractional b) => Fractional    (a :> b)
deriving instance (VectorSpace b b, LMapDom a b, Floating b  ) => Floating      (a :> b)
deriving instance (VectorSpace b s, LMapDom a s              ) => AdditiveGroup (a :> b)


inT :: ((a D.:> b) -> (c D.:> d))
    -> ((a   :> b) -> (c   :> d))
inT  = (T .).(. unT)

inT2 :: ((a D.:> b) -> (c D.:> d) -> (e D.:> f))
     -> ((a   :> b) -> (c   :> d) -> (e   :> f))
inT2  = (inT .).(. unT)

inT3 :: ((a D.:> b) -> (c D.:> d) -> (e D.:> f) -> (g D.:> h))
     -> ((a   :> b) -> (c   :> d) -> (e   :> f) -> (g   :> h))
inT3  = (inT2 .).(. unT)

-- | Extract the value from a derivative tower
powVal :: (a :> b) -> b
powVal = D.powVal . unT

-- | Extract the derivative from a derivative tower
derivative :: (VectorSpace b s, LMapDom a s) =>
              (a :> b) -> (a :-* (a :> b))
derivative = fmapL T . D.derivative . unT

-- | Sampled derivative.  For avoiding an awkward typing problem related
-- to the two required 'VectorSpace' instances.
derivativeAt :: (LMapDom a s, VectorSpace b s) =>
                (a :> b) -> a -> (a :> b)
derivativeAt d = T . D.derivativeAt (unT d)

-- The definition of 'derivativeAt' takes care to share partial
-- applications of 'D.derivativeAt', which is useful in power series
-- representations for which 'derivative' is not free (Horner).

-- | Infinitely differentiable functions
type a :~> b = a -> (a:>b)

-- -- Handy for missing methods.
-- noOv :: String -> a
-- noOv op = error (op ++ ": not defined on a :> b")


-- | Derivative tower full of 'zeroV'.
dZero :: (LMapDom a s, VectorSpace b s) => a:>b
dZero = T D.dZero


-- | Constant derivative tower.
pureD :: (LMapDom a s, VectorSpace b s) => b -> a:>b
pureD = fmap T D.pureD

-- | Map a /linear/ function over a derivative tower.
fmapD, (<$>>) :: (LMapDom a s, VectorSpace b s) =>
                 (b -> c) -> (a :> b) -> (a :> c)
fmapD = fmap inT D.fmapD

(<$>>) = fmapD

-- -- | Like '(<*>)' for derivative towers.
-- (<*>>) :: (LMapDom a s, VectorSpace b s, VectorSpace c s) =>
--           (a :> (b -> c)) -> (a :> b) -> (a :> c)
-- (<*>>) = inT2 (D.<*>>)

-- | Apply a /linear/ binary function over derivative towers.
liftD2 :: (VectorSpace b s, LMapDom a s, VectorSpace c s, VectorSpace d s) =>
          (b -> c -> d) -> (a :> b) -> (a :> c) -> (a :> d)
liftD2 = fmap inT2 D.liftD2


-- | Apply a /linear/ ternary function over derivative towers.
liftD3 :: ( LMapDom a s
          , VectorSpace b s, VectorSpace c s
          , VectorSpace d s, VectorSpace e s ) =>
          (b -> c -> d -> e)
       -> (a :> b) -> (a :> c) -> (a :> d) -> (a :> e)
liftD3 = fmap inT3 D.liftD3

-- | Differentiable identity function.  Sometimes called "the
-- derivation variable" or similar, but it's not really a variable.
idD :: (LMapDom u s, VectorSpace u s) => u :~> u
idD = fmap T D.idD

-- | Every linear function has a constant derivative equal to the function
-- itself (as a linear map).
linearD :: (LMapDom u s, VectorSpace v s) => (u -> v) -> (u :~> v)
linearD = (fmap.fmap) T D.linearD

-- Other examples of linear functions

-- | Differentiable version of 'fst'
fstD :: (VectorSpace a s, LMapDom b s, LMapDom a s) => (a,b) :~> a
fstD = fmap T D.fstD

-- | Differentiable version of 'snd'
sndD :: (VectorSpace b s, LMapDom b s, LMapDom a s) => (a,b) :~> b
sndD = fmap T D.sndD

-- | Derivative tower for applying a binary function that distributes over
-- addition, such as multiplication.  A bit weaker assumption than
-- bilinearity.
distrib :: (LMapDom a s, VectorSpace b s, VectorSpace c s, VectorSpace u s) =>
           (b -> c -> u) -> (a :> b) -> (a :> c) -> (a :> u)
distrib = fmap inT2 D.distrib

-- I'm not sure about the next three, which discard information

instance Show b => Show (a :> b) where show    = show     .   unT
instance Eq   b => Eq   (a :> b) where (==)    = (==)    `on` unT
instance Ord  b => Ord  (a :> b) where compare = compare `on` unT

-- These next two instances are the reason for having this module.  The
-- scalar field differs from the one used in the underlying
-- representation.  I can't have both instances.  First, there is a
-- functional dependency on 'VectorSpace', which says that a vector space
-- type determines its scalar field type.  I experimented with dropping
-- the fundep, and then managing the resulting ambiguity.  However,
-- the two 'VectorSpace' instances overlap considerably.

instance (LMapDom a s, VectorSpace u s, VectorSpace s s)
    => VectorSpace (a :> u) (a :> s) where
  (*^)    = inT2 (D.**^) -- not '(D.*^)'

instance (InnerSpace u s, InnerSpace s s', VectorSpace s s, LMapDom a s) =>
     InnerSpace (a :> u) (a :> s) where
  (<.>)    = inT2 (D.<*.>) -- not '(D.<.>)'


-- | Chain rule.
(@.) :: (LMapDom b s, LMapDom a s, VectorSpace c s) =>
        (b :~> c) -> (a :~> b) -> (a :~> c)
h @. g = T . ((unT . h) D.@. (unT . g))

-- | Specialized chain rule.
(>-<) :: (LMapDom a s, VectorSpace s s, VectorSpace u s) =>
         (u -> u) -> ((a :> u) -> (a :> s))
      -> (a :> u) -> (a :> u)
f >-< f' = inT (f D.>-< (unT . f' . T))
