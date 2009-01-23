{-# LANGUAGE TypeOperators, MultiParamTypeClasses, UndecidableInstances
           , TypeSynonymInstances, FlexibleInstances
           , FlexibleContexts, TypeFamilies
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
    (:>), powVal, derivative
  , (:~>), dZero, pureD
  , fmapD, (<$>>){-, (<*>>)-}, liftD2, liftD3
  , idD, fstD, sndD
  , linearD, distrib
  -- , (@.)
  , (>-<)
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

-- Handy for missing methods.
noOv :: String -> a
noOv op = error (op ++ ": not defined on a :> b")

-- | Derivative tower full of 'zeroV'.
dZero :: (AdditiveGroup b, HasBasis a, HasTrie (Basis a)) => a:>b
dZero = pureD zeroV

-- | Constant derivative tower.
pureD :: (AdditiveGroup b, HasBasis a, HasTrie (Basis a)) => b -> a:>b
pureD b = b `D` pure dZero


infixl 4 <$>>
-- | Map a /linear/ function over a derivative tower.
fmapD, (<$>>) :: (HasTrie (Basis a)) =>
                 (b -> c) -> (a :> b) -> (a :> c)
fmapD f (D b0 b') = D (f b0) ((fmap.fmapD) f b')

(<$>>) = fmapD

-- | Apply a /linear/ binary function over derivative towers.
liftD2 :: HasTrie (Basis a) =>
          (b -> c -> d) -> (a :> b) -> (a :> c) -> (a :> d)
liftD2 f (D b0 b') (D c0 c') = D (f b0 c0) (liftA2 (liftD2 f) b' c')


-- | Apply a /linear/ ternary function over derivative towers.
liftD3 :: HasTrie (Basis a) =>
          (b -> c -> d -> e)
       -> (a :> b) -> (a :> c) -> (a :> d) -> (a :> e)
liftD3 f (D b0 b') (D c0 c') (D d0 d') = D (f b0 c0 d0) (liftA3 (liftD3 f) b' c' d')

-- TODO: Define liftD2, liftD3 in terms of (<*>>) Compare generated code
-- for speed.

-- infixl 4 <*>>
-- -- | Like '(<*>)' for derivative towers.
-- (<*>>) :: (HasTrie (Basis a)) =>
--           (a :> (b -> c)) -> (a :> b) -> (a :> c)
-- D f0 f' <*>> D x0 x' = D (f0 x0) (liftA2 (<*>>) f' x')

-- liftD2 f a b = (f <$>> a) <*>> b

-- liftD3 f a b c = liftD2 f a b <*>> c


-- | Differentiable identity function.  Sometimes called "the
-- derivation variable" or similar, but it's not really a variable.
idD :: ( VectorSpace u, s ~ Scalar u
       , VectorSpace (u :> u), VectorSpace s
       , HasBasis u, HasTrie (Basis u)) =>
       u :~> u
idD = linearD id

-- or
--   dId v = D v pureD

-- | Every linear function has a constant derivative equal to the function
-- itself (as a linear map).
linearD :: (HasBasis u, HasTrie (Basis u), AdditiveGroup v) =>
           (u -> v) -> (u :~> v)

-- linearD f u = f u `D` linear (pureD . f)

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

linearD f = \ u -> f u `D` d
 where
   d = linear (pureD . f)

-- (`D` d) . f

-- linearD f = (`D` linear (pureD . f)) . f


-- Other examples of linear functions

-- | Differentiable version of 'fst'
fstD :: ( HasBasis a, HasTrie (Basis a)
        , HasBasis b, HasTrie (Basis b)
        , Scalar a ~ Scalar b
        ) => (a,b) :~> a
fstD = linearD fst

-- | Differentiable version of 'snd'
sndD :: ( HasBasis a, HasTrie (Basis a)
        , HasBasis b, HasTrie (Basis b)
        , Scalar a ~ Scalar b
        ) => (a,b) :~> b
sndD = linearD snd

-- | Derivative tower for applying a binary function that distributes over
-- addition, such as multiplication.  A bit weaker assumption than
-- bilinearity.
distrib :: forall a b c u.
           (HasBasis a, HasTrie (Basis a), AdditiveGroup u) =>
           (b -> c -> u) -> (a :> b) -> (a :> c) -> (a :> u)

-- distrib op u@(D u0 u') v@(D v0 v') =
--   D (u0 `op` v0) (trie (\ e -> distrib op u (v' `untrie` e) ^+^
--                                distrib op (u' `untrie` e) v))

distrib op u@(D u0 u') v@(D v0 v') = D (u0 `op` v0) (inTrie2 comb u' v')
 where
   -- comb :: (Basis a -> a :> b) -> (Basis a -> a :> c) -> (Basis a -> a :> u)
   comb uf vf (e :: Basis a) =
     distrib op u (vf e) ^+^ distrib op (uf e) v

--   comb uf vf = distrib op u . vf ^+^ flip (distrib op) v . uf

-- TODO: Look for a formulation of distrib that eliminates the explicit
-- conversion between functions and tries.  Maybe something with trie addition.


-- TODO: I think this distrib is exponential in increasing degree.  Switch
-- to the Horner representation.  See /The Music of Streams/ by Doug
-- McIlroy.


instance Show b => Show (a :> b) where show    = noOv "show"
instance Eq   b => Eq   (a :> b) where (==)    = noOv "(==)"
instance Ord  b => Ord  (a :> b) where compare = noOv "compare"

instance (HasBasis a, HasTrie (Basis a), AdditiveGroup u) => AdditiveGroup (a :> u) where
  zeroV   = pureD  zeroV    -- or dZero
  negateV = fmapD  negateV
  (^+^)   = liftD2 (^+^)

instance (HasBasis a, HasTrie (Basis a), VectorSpace u)
      => VectorSpace (a :> u) where
  type Scalar (a :> u) = (a :> Scalar u)
  (*^) = distrib (*^)                     

instance ( InnerSpace u, s ~ Scalar u, AdditiveGroup s
         , HasBasis a, HasTrie (Basis a) ) =>
     InnerSpace (a :> u) where
  (<.>) = distrib (<.>)

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
(>-<) :: (HasBasis a, HasTrie (Basis a), VectorSpace u) =>
         (u -> u) -> ((a :> u) -> (a :> Scalar u))
      -> (a :> u) -> (a :> u)
f >-< f' = \ u@(D u0 u') -> D (f u0) (f' u *^ u')


-- TODO: express '(>-<)' in terms of '(@.)'.  If I can't, then understand why not.

instance ( HasBasis a, s ~ Scalar a, HasTrie (Basis a)
         , Num s, VectorSpace s, Scalar s ~ s
         )
      => Num (a:>s) where
  fromInteger = pureD . fromInteger
  (+) = liftD2  (+)
  (-) = liftD2  (-)
  (*) = distrib (*)
  negate = negate >-< -1
  abs    = abs    >-< signum
  signum = signum >-< 0  -- derivative wrong at zero

instance ( HasBasis a, s ~ Scalar a, HasTrie (Basis a)
         , Fractional s, VectorSpace s, Scalar s ~ s)
         => Fractional (a:>s) where
  fromRational = pureD . fromRational
  recip        = recip >-< recip sqr

sqr :: Num a => a -> a
sqr x = x*x

instance ( HasBasis a, s ~ Scalar a, HasTrie (Basis a)
         , Floating s, VectorSpace s, Scalar s ~ s)
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
