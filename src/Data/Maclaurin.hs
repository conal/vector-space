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
    (:>)(D), powVal, derivative, derivAtBasis  -- maybe not D
  , (:~>), pureD
  , fmapD, (<$>>){-, (<*>>)-}, liftD2, liftD3
  , idD, fstD, sndD
  , linearD, distrib
  -- , (@.)
  , (>-<)
  -- * Misc
  , pairD, unpairD, tripleD, untripleD
  ) 
    where

-- import Control.Applicative (liftA2)
import Data.Function (on)

import Data.VectorSpace
import Data.NumInstances ()
import Data.MemoTrie
import Data.Basis
import Data.LinearMap

import Data.Boolean

infixr 9 `D`
-- | Tower of derivatives.
data a :> b = D { powVal :: b, derivative :: a :-* (a :> b) }

-- | Infinitely differentiable functions
type a :~> b = a -> (a:>b)

-- Handy for missing methods.
noOv :: String -> a
noOv op = error (op ++ ": not defined on a :> b")

-- | Constant derivative tower.
pureD :: (AdditiveGroup b, HasBasis a, HasTrie (Basis a)) => b -> a:>b
pureD b = b `D` zeroV


infixl 4 <$>>
-- | Map a /linear/ function over a derivative tower.
fmapD, (<$>>) :: (HasBasis a, HasTrie (Basis a), AdditiveGroup b) =>
                 (b -> c) -> (a :> b) -> (a :> c)
fmapD f = lf
 where
   lf (D b0 b') = D (f b0) ((inLMap.liftL) lf b')

(<$>>) = fmapD

-- | Apply a /linear/ binary function over derivative towers.
liftD2 :: (HasBasis a, HasTrie (Basis a), AdditiveGroup b, AdditiveGroup c) =>
          (b -> c -> d) -> (a :> b) -> (a :> c) -> (a :> d)
liftD2 f = lf
 where
   lf (D b0 b') (D c0 c') = D (f b0 c0) ((inLMap2.liftL2) lf b' c')


-- | Apply a /linear/ ternary function over derivative towers.
liftD3 :: (HasBasis a, HasTrie (Basis a)
          , AdditiveGroup b, AdditiveGroup c, AdditiveGroup d) =>
          (b -> c -> d -> e)
       -> (a :> b) -> (a :> c) -> (a :> d) -> (a :> e)
liftD3 f = lf
 where
   lf (D b0 b') (D c0 c') (D d0 d') =
     D (f b0 c0 d0) ((inLMap3.liftL3) lf b' c' d')


-- TODO: Can liftD2 and liftD3 be defined in terms of a (<*>>) similar to
-- (<*>)?  If so, can the speed be as good?

-- liftD2 f a b = (f <$>> a) <*>> b
-- 
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
-- bilinearity.  Is bilinearity necessary for correctness here?
distrib :: forall a b c u.
           ( HasBasis a, HasTrie (Basis a)
           , AdditiveGroup b, AdditiveGroup c, AdditiveGroup u) =>
           (b -> c -> u) -> (a :> b) -> (a :> c) -> (a :> u)

distrib op = (#)
 where
   u@(D u0 u') # v@(D v0 v') =
     D (u0 `op` v0) ( (inLMap.liftMS) (inTrie ((# v) .)) u' ^+^
                      (inLMap.liftMS) (inTrie ((u #) .)) v' )


-- TODO: I think this distrib is exponential in increasing degree.  Switch
-- to the Horner representation.  See /The Music of Streams/ by Doug
-- McIlroy.


-- instance Show b => Show (a :> b) where show    = noOv "show"

instance Show b => Show (a :> b) where
  show (D b0 _) = "D " ++ show b0  ++ " ..."

instance Eq   b => Eq   (a :> b) where (==)    = noOv "(==)"

type instance BooleanOf (a :> b) = BooleanOf b

instance (AdditiveGroup v, HasBasis u, HasTrie (Basis u), IfB v) =>
      IfB (u :> v) where
  ifB = liftD2 . ifB

instance (AdditiveGroup v, HasBasis u, HasTrie (Basis u), OrdB v) =>
         OrdB (u :> v) where
  (<*) = (<*) `on` powVal

instance ( AdditiveGroup b, HasBasis a, HasTrie (Basis a)
         , OrdB b, IfB b, Ord  b) => Ord  (a :> b) where
  compare = compare `on` powVal
  min     = minB
  max     = maxB

-- minB & maxB use ifB, and so can work even if b is an expression type,
-- as in deep DSELs.

instance (HasBasis a, HasTrie (Basis a), AdditiveGroup u) => AdditiveGroup (a :> u) where
  zeroV   = pureD  zeroV
  negateV = fmapD  negateV
  D a0 a' ^+^ D b0 b' = D (a0 ^+^ b0) (a' ^+^ b')
  -- Less efficient: adds zero
  -- (^+^)   = liftD2 (^+^)

instance ( HasBasis a, HasTrie (Basis a)
         , VectorSpace u, AdditiveGroup (Scalar u) )
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
(>-<) :: ( HasBasis a, HasTrie (Basis a), VectorSpace u
         , AdditiveGroup (Scalar u)) =>
         (u -> u) -> ((a :> u) -> (a :> Scalar u))
      -> (a :> u) -> (a :> u)
f >-< f' = \ u@(D u0 u') -> D (f u0) ((inLMap.liftMS) (f' u *^) u')


-- TODO: express '(>-<)' in terms of '(@.)'.  If I can't, then understand why not.

instance ( HasBasis a, s ~ Scalar a, HasTrie (Basis a)
         , Num s, VectorSpace s, Scalar s ~ s
         )
      => Num (a:>s) where
  fromInteger = pureD . fromInteger
  (+)    = (^+^)
  (*)    = distrib (*)
  negate = negate >-< -1
  abs    = abs    >-< signum
  signum = signum >-< 0  -- derivative wrong at zero

instance ( HasBasis a, s ~ Scalar a, HasTrie (Basis a)
         , Fractional s, VectorSpace s, Scalar s ~ s)
         => Fractional (a:>s) where
  fromRational = pureD . fromRational
  recip        = recip >-< - recip sqr

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


-- | Sample the derivative at a basis element.  Optimized for partial
-- application to save work for non-scalar derivatives.
derivAtBasis :: (HasTrie (Basis a), HasBasis a, AdditiveGroup b) =>
                (a :> b) -> (Basis a -> (a :> b))
derivAtBasis f = atBasis (derivative f)


---- Misc

pairD :: ( HasBasis a, HasTrie (Basis a)
         , VectorSpace b, VectorSpace c
         , Scalar b ~ Scalar c
         ) => (a:>b,a:>c) -> a:>(b,c)

pairD (u,v) = liftD2 (,) u v

unpairD :: ( HasBasis a, HasTrie (Basis a)
           , VectorSpace a, VectorSpace b, VectorSpace c
           , Scalar b ~ Scalar c
           ) => (a :> (b,c)) -> (a:>b, a:>c)
unpairD d = (fst <$>> d, snd <$>> d)


tripleD :: ( HasBasis a, HasTrie (Basis a)
           , VectorSpace b, VectorSpace c, VectorSpace d
           , Scalar b ~ Scalar c, Scalar c ~ Scalar d
           ) => (a:>b,a:>c,a:>d) -> a:>(b,c,d)
tripleD (u,v,w) = liftD3 (,,) u v w

untripleD :: ( HasBasis a, HasTrie (Basis a)
             , VectorSpace a, VectorSpace b, VectorSpace c, VectorSpace d
             , Scalar b ~ Scalar c, Scalar c ~ Scalar d
             ) =>
             (a :> (b,c,d)) -> (a:>b, a:>c, a:>d)
untripleD d =
  ((\ (a,_,_) -> a) <$>> d, (\ (_,b,_) -> b) <$>> d, (\ (_,_,c) -> c) <$>> d)

