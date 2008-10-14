{-# LANGUAGE TypeOperators, MultiParamTypeClasses, UndecidableInstances
           , TypeSynonymInstances, FlexibleInstances, FunctionalDependencies
           , FlexibleContexts
           , ScopedTypeVariables
  #-}

-- The ScopedTypeVariables is there just as a bug work-around.  Without it
-- I get a bogus error about context mismatch for mutually recursive
-- definitions.  This bug was introduced between ghc 6.9.20080622 and
-- 6.10.0.20081007.


-- {-# OPTIONS_GHC -ddump-simpl-stats -ddump-simpl #-}

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
    (:>), powVal, derivative --, derivativeAt
  , (:~>), dZero, pureD
  , fmapD, (<$>>){-, (<*>>)-}, liftD2, liftD3
  , idD -- , fstD, sndD
  , linearD, distrib
  -- , (@.)
  , (>-<)
  ,(**^), (<*.>)
  -- , HasDeriv(..)
  -- experimental
  -- , liftD3
  ) 
    where

import Control.Applicative

import Data.VectorSpace
import Data.NumInstances ()
import Data.MemoTrie
import Data.Basis
import Data.LinearMap


infixr 9 `D`
-- | Tower of derivatives.
data a :> b = D { powVal :: b, derivative :: a :-* (a :> b) }

-- | Infinitely differentiable functions
type a :~> b = a -> (a:>b)

-- -- | Sampled derivative.  For avoiding an awkward typing problem related
-- -- to the two required 'VectorSpace' instances.
-- derivativeAt :: (VectorSpace b s) =>
--                 (a :> b) -> a -> (a :> b)
-- derivativeAt d = lapply (derivative d)

-- The crucial point here is for 'lapply' to be interpreted with respect to
-- the 'VectorSpace' instance in this module, not Mac.

-- The argument order for 'derivativeAt' allows partial evaluation, which
-- is useful in power series representations for which 'derivative' is not
-- free (Horner).

-- Handy for missing methods.
noOv :: String -> a
noOv op = error (op ++ ": not defined on a :> b")

-- | Derivative tower full of 'zeroV'.
dZero :: (AdditiveGroup b, HasBasis a s, HasTrie (Basis a)) => a:>b
dZero = pureD zeroV

-- | Constant derivative tower.
pureD :: (AdditiveGroup b, HasBasis a s, HasTrie (Basis a)) => b -> a:>b
pureD b = b `D` pure dZero


infixl 4 <$>>
-- | Map a /linear/ function over a derivative tower.
fmapD, (<$>>) :: (HasTrie (Basis a), VectorSpace b s) =>
                 (b -> c) -> (a :> b) -> (a :> c)
fmapD f (D b0 b') = D (f b0) ((fmap.fmapD) f b')

(<$>>) = fmapD

-- infixl 4 <*>>
-- -- | Like '(<*>)' for derivative towers.
-- (<*>>) :: (HasTrie (Basis a), VectorSpace b s, VectorSpace c s) =>
--           (a :> (b -> c)) -> (a :> b) -> (a :> c)
-- D f0 f' <*>> D x0 x' = D (f0 x0) (liftA2 (<*>>) f' x')

-- | Apply a /linear/ binary function over derivative towers.
liftD2 :: (HasTrie (Basis a), VectorSpace b s, VectorSpace c s, VectorSpace d s) =>
          (b -> c -> d) -> (a :> b) -> (a :> c) -> (a :> d)
liftD2 f (D b0 b') (D c0 c') = D (f b0 c0) (liftA2 (liftD2 f) b' c')

-- | Apply a /linear/ ternary function over derivative towers.
liftD3 :: ( HasTrie (Basis a)
          , VectorSpace b s, VectorSpace c s
          , VectorSpace d s, VectorSpace e s ) =>
          (b -> c -> d -> e)
       -> (a :> b) -> (a :> c) -> (a :> d) -> (a :> e)
liftD3 f (D b0 b') (D c0 c') (D d0 d') = D (f b0 c0 d0) (liftA3 (liftD3 f) b' c' d')

-- TODO: try defining liftD2, liftD3 in terms of (<*>>) above

-- | Differentiable identity function.  Sometimes called "the
-- derivation variable" or similar, but it's not really a variable.
idD :: ( VectorSpace u s, VectorSpace (u :> u) (u :> s), VectorSpace s s
       , HasBasis u s, HasTrie (Basis u)) =>
       u :~> u
idD = linearD id

-- or
--   dId v = D v pureD

-- | Every linear function has a constant derivative equal to the function
-- itself (as a linear map).
linearD :: ( HasBasis u s, HasTrie (Basis u){-, VectorSpace (u :> v) s, -}
           , VectorSpace v s, VectorSpace s s ) =>
           (u -> v) -> (u :~> v)

-- linearD f u = f u `D` linear (pureD . f)

-- data a :> b = D { powVal :: b, derivative :: a :-* (a :> b) }

-- linear :: (VectorSpace u s, VectorSpace v s, HasBasis u s, HasTrie (Basis u)) =>
--           (u -> v) -> (u :-* v)


-- HEY!  I think there's a hugely wasteful recomputation going on in
-- 'linearD' above.  Note the definition of 'linear':
-- 
--     linear f = trie (f . basisValue)
-- 
-- Substituting,
-- 
--     linearD f u = f u `D` trie ((pureD . f) . basisValue)
-- 
-- The trie gets rebuilt for each @u@.

-- Look for similar problems.

-- 

linearD f = \ u -> f u `D` d
 where
   d = linear (pureD . f)

-- (`D` d) . f

-- linearD f = (`D` linear (pureD . f)) . f



-- TODO: revise two previous signatures when i've added the VectorSpace instance for u:>v

{-

-- Other examples of linear functions

-- | Differentiable version of 'fst'
fstD :: -- (VectorSpace a s, HasBasis a s, HasTrie (Basis a), HasBasis b s, HasTrie (Basis b)) =>
        ( HasBasis a s, HasTrie (Basis a)
        , HasBasis b s, HasTrie (Basis b)
        , HasBasis (a,b) s, HasTrie (Basis (a, b))
        ) =>
        (a,b) :~> a
fstD = linearD fst

-- wtf:
-- 
--   Data/NewMaclaurin.hs:138:7:
--       Could not deduce (HasTrie (Basis (a, b)))
--         from the context (HasBasis a s,
--                           HasTrie (Basis a),
--                           HasBasis b s,
--                           HasTrie (Basis b),
--                           HasBasis (a, b) s,
--                           HasTrie (Basis (a, b)))
--         arising from a use of `linearD' at Data/NewMaclaurin.hs:138:7-17
--       Possible fix:
--         add (HasTrie (Basis (a, b))) to the context of
--           the type signature for `fstD'
--         or add an instance declaration for (HasTrie (Basis (a, b)))
--       In the expression: linearD fst
--       In the definition of `fstD': fstD = linearD fst
--   Failed, modules loaded: Data.MemoTrie, Data.Basis, Data.VectorSpace, Data.AdditiveGroup, Data.NumInstances.
--   *Data.Basis> 

-- -- | Differentiable version of 'snd'
-- sndD :: (VectorSpace b s, HasBasis b s, HasTrie (Basis b), HasTrie (Basis a)) => (a,b) :~> b
-- sndD = linearD snd

-}

-- | Derivative tower for applying a binary function that distributes over
-- addition, such as multiplication.  A bit weaker assumption than
-- bilinearity.
distrib :: ( HasBasis a s, HasTrie (Basis a)
           , VectorSpace b s, VectorSpace c s, VectorSpace u s) =>
           (b -> c -> u) -> (a :> b) -> (a :> c) -> (a :> u)

distrib op u@(D u0 u') v@(D v0 v') =
  D (u0 `op` v0) (trie (\ da -> distrib op u (v' `untrie` da) ^+^
                                distrib op (u' `untrie` da) v))

-- TODO: look for a simpler definition of distrib.  See inTrie2.

-- TODO: This distrib is exponential in increasing degree.  Switch to the
-- Horner representation.  See /The Music of Streams/ by Doug McIlroy.


-- I'm not sure about the next three, which discard information

instance Show b => Show (a :> b) where show    = noOv "show"
instance Eq   b => Eq   (a :> b) where (==)    = noOv "(==)"
instance Ord  b => Ord  (a :> b) where compare = noOv "compare"

instance (HasBasis a s, HasTrie (Basis a), VectorSpace u s) => AdditiveGroup (a :> u) where
  zeroV   = pureD  zeroV    -- or dZero
  negateV = fmapD  negateV
  (^+^)   = liftD2 (^+^)

{-
instance (HasBasis a s, HasTrie (Basis a), VectorSpace u s) => VectorSpace (a :> u) s where
  (*^) s = fmapD  ((*^) s)
-}

(**^) :: (HasBasis a s, HasTrie (Basis a), VectorSpace c s, VectorSpace s s) =>
         (a :> s) -> (a :> c) -> (a :> c)
(**^) = distrib (*^)

-- ouch!  InnerSpace one won't work at all, for the same reason as for functions.

-- instance (InnerSpace u s) => InnerSpace (a :> u) s where
--   (<.>) = distrib (<.>)

(<*.>) :: (HasBasis a s, HasTrie (Basis a), InnerSpace b s, VectorSpace s s) =>
          (a :> b) -> (a :> b) -> (a :> s)
(<*.>) = distrib (<.>)


-- The instances below are the one I think we'll want externally.
-- However, the ones above allow the definition of @a:>b@ to work out.
-- The module "Data.Mac" rewraps to provide the alternate instances.

instance (HasBasis a s, HasTrie (Basis a), VectorSpace u s, VectorSpace s s)
         => VectorSpace (a :> u) (a :> s) where
  (*^) = (**^)

instance ( InnerSpace u s, InnerSpace s s', VectorSpace s s
         , HasBasis a s, HasTrie (Basis a)) =>
     InnerSpace (a :> u) (a :> s) where
  (<.>) = (<*.>)


-- infixr 9 @.
-- -- | Chain rule.  See also '(>-<)'.
-- (@.) :: (HasTrie (Basis b), HasTrie (Basis a), VectorSpace c s) =>
--         (b :~> c) -> (a :~> b) -> (a :~> c)
-- (h @. g) a0 = D c0 (inL2 (@.) c' b')
--   where
--     D b0 b' = g a0
--     D c0 c' = h b0

infix  0 >-<

-- | Specialized chain rule.  See also '(\@.)'
(>-<) :: (HasBasis a s, HasTrie (Basis a), VectorSpace s s, VectorSpace u s) =>
         (u -> u) -> ((a :> u) -> (a :> s))
      -> (a :> u) -> (a :> u)
f >-< f' = \ u@(D u0 u') -> D (f u0) ((f' u **^) <$> u')

-- TODO: express '(>-<)' in terms of '(@.)'.  If I can't, then understand why not.

instance (HasBasis a s, HasTrie (Basis a), Num s, VectorSpace s s) => Num (a:>s) where
  fromInteger = pureD . fromInteger
  (+) = liftD2  (+)
  (-) = liftD2  (-)
  (*) = distrib (*)
  negate = negate >-< -1
  abs    = abs    >-< signum
  signum = signum >-< 0  -- derivative wrong at zero

instance (HasBasis a s, HasTrie (Basis a), Fractional s, VectorSpace s s)
         => Fractional (a:>s) where
  fromRational = pureD . fromRational
  recip        = recip >-< recip sqr

sqr :: Num a => a -> a
sqr x = x*x

instance (HasBasis a s, HasTrie (Basis a), Floating s, VectorSpace s s)
         => Floating (a:>s) where
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
