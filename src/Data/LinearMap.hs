{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances
           , MultiParamTypeClasses, FlexibleInstances
           , FunctionalDependencies
  #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans -fglasgow-exts #-}
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
    LMapDom(..), inL, inL2, inL3
  , linearK, (.*)
  , pureL {-, (<*>*)-}, fmapL, (<$>*), liftL2, liftL3, idL
  ) where

-- -fglasgow-exts above enables the RULES pragma

import Control.Applicative
import Data.Function

import Data.VectorSpace

-- Temporary
import Graphics.Rendering.OpenGL.GL.CoordTrans
  (Vector2(..),Vector3(..))


infixr 9 :-*
infixr 9 .*
infixl 9 $*
infixl 4 {-<*>*,-} <$>*


-- | Domain of a linear map.
class VectorSpace a s => LMapDom a s | a -> s where
  -- | Linear map type
  data (:-*) a :: * -> *
  -- | Linear map as function
  ($*) :: VectorSpace b s => (a :-* b) -> (a -> b)
  -- | Function (assumed linear) as linear map.
  linear :: (a -> b) -> (a :-* b)

-- Neither 'VectorSpace' nor even 'AdditiveGroup' is really required as a
-- 'LMapDom' superclass.  Instead, we could have additional constraints in
-- some 'LMapDom' instances and related functions.


{-# RULES
"linear.($*)"   forall m. linear (($*) m) = m
"($*).linear"   forall f. ($*) (linear f) = f
 #-}


-- | Transform a linear map by transforming a linear function.
inL :: (LMapDom c s, VectorSpace b s', LMapDom a s') =>
        ((a -> b) -> (c -> d)) -> ((a :-* b) -> (c :-* d))
{-# INLINE inL #-}
inL h = linear . h . ($*)

-- | Transform a linear maps by transforming linear functions.
inL2 :: ( LMapDom c s, VectorSpace b s', LMapDom a s'
        , LMapDom e s, VectorSpace d s ) =>
        ((a -> b) -> (c -> d) -> (e -> f))
     -> ((a :-* b) -> (c :-* d) -> (e :-* f))
{-# INLINE inL2 #-}
inL2 h = inL . h . ($*)

-- inL2 h m n
--   = (inL . h . ($*)) m n
--   = inL (h (($*) m)) n
--   = (linear . (h (($*) m)) . ($*)) n
--   = linear (h (($*) m) (($*) n)
--   = linear (h (m $*) (n $*))


-- | Transform a linear maps by transforming linear functions.
inL3 :: ( LMapDom a s, VectorSpace b s
        , VectorSpace f s , LMapDom p s, LMapDom c s'
        , VectorSpace d s', LMapDom e s ) =>
        ((a -> b) -> (c -> d) -> (e -> f) -> (p -> q))
     -> ((a :-* b) -> (c :-* d) -> (e :-* f) -> (p :-* q))
{-# INLINE inL3 #-}
inL3 h = inL2 . h . ($*)


-- TODO: go through this whole module and relax constraints on scalar
-- fields.  See if it helps with the scalar dilemma in Mac2


-- | Constant value as a linear map
pureL :: LMapDom a s => b -> (a :-* b)
pureL b = linear (const b)

-- -- | Like '(<*>)' for linear maps.
-- (<*>*) :: (LMapDom a s, VectorSpace b s, VectorSpace c s) =>
--         (a :-* (b -> c)) -> (a :-* b) -> (a :-* c)
-- (<*>*) = inL2 (<*>)

-- | Map a /linear/ function over a linear map.
fmapL, (<$>*) :: (LMapDom a s, VectorSpace b s) =>
                 (b -> c) -> (a :-* b) -> (a :-* c)
{-# INLINE fmapL #-}
fmapL = inL . fmap

-- fmapL f
--   = inL (f .)
--   = linear . (f .) . ($*)
--   = \ m -> linear (fmap f (m $*))

(<$>*) = fmapL


{-# RULES
"fmapL.fmapL"  forall f g m. fmapL f (fmapL g m) = fmapL (f.g) m
 #-}

-- | Apply a /linear/ binary function over linear maps.
liftL2 :: ( LMapDom a s, VectorSpace b s
           , VectorSpace c s, VectorSpace d s) =>
           (b -> c -> d) -> (a :-* b) -> (a :-* c) -> (a :-* d)
liftL2 = inL2 . liftA2

-- liftL2 f a b
--   = inL2 (liftA2 f) a b
--   = linear (liftA2 f (a $*) (b $*))

-- I expected the following definition to be equivalent, thanks to rewriting:
-- 
--   liftL2 f b c = fmapL f b <*>* c
--     = linear (f . ($*) b) <*>* c
--     = linear (($*) (linear (f . ($*) b)) <*> ($*) c)
--     = linear ((f . ($*) b) <*> ($*) c)
--     = linear (liftA2 f (b $*) (c $*))
--     = (inL2.liftA2) f b c

-- The rewrite isn't happening, however.  And the '(<*>*)' definition
-- yields an incredibly slow implementation.
-- 
-- Here's that derivation again, in slo-mo:

--   liftL2 f b c
--     = fmapL f b <*>* c                              -- inline liftL2
--     = inL (f .) b <*>* c                            -- inline fmapL
--     = (linear . (f .) ($*)) b <*>* c                -- inline inL
--     = linear (f . ($*) b) <*>* c                    -- inline (.)
--     = inL2 (<*>) (linear (f . ($*) b)) c            -- inline (<*>*)
--     = (inL . (<*>) . ($*)) (linear (f . ($*) b)) c  -- inline inL2
--     = inL ((<*>) (($*) (linear (f . ($*) b)))) c    -- inline (.)
--     = inL ((<*>) (f . ($*) b)) c                    -- RULE ($*).linear
--     = (linear . ((<*>) (f . ($*) b)) .($*)) c       -- inline inL
--     = linear ((<*>) (f . ($*) b) (($*) c))          -- inline (.)
--     = linear ((f . ($*) b) <*> (($*) c))            -- infix <*>
--     = linear ((f <$> ($*) b) <*> (($*) c))          -- <$> on (a ->)
--     = linear (liftA2 f (b $*) (c $*))               -- uninline liftA2

-- When I compile this module, I don't get any firings of ($*).linear


-- | Apply a /linear/ ternary function over linear maps.
liftL3 :: ( LMapDom a s, VectorSpace b s, VectorSpace c s
           , VectorSpace d s, VectorSpace e s) =>
           (b -> c -> d -> e)
        -> (a :-* b) -> (a :-* c) -> (a :-* d) -> (a :-* e)
liftL3 = inL3 . liftA3


-- TODO: Get clear about the linearity requirements of 'apL', 'liftL2',
-- and 'liftL3'.

-- | Identity linear map
idL :: LMapDom a s => a :-* a
idL = linear id

-- | Compose linear maps
(.*) :: (VectorSpace c s, LMapDom b s, LMapDom a s) =>
        (b :-* c) -> (a :-* b) -> (a :-* c)
(.*) = inL2 (.)


instance (VectorSpace v s, LMapDom u s) => AdditiveGroup (u :-* v) where
  zeroV   = pureL  zeroV
  (^+^)   = liftL2 (^+^)
  negateV = fmapL  negateV

instance (VectorSpace v s, LMapDom u s) => VectorSpace (u :-* v) s where
  (*^) s  = fmapL  (s *^)

-- Or possibly the following non-standard definition:

-- instance (VectorSpace v s, VectorSpace s s, LMapDom u s)
--       => VectorSpace (u :-* v) (u :-* s) where
--   zeroV   = pureL  zeroV
--   (*^)    = liftL2 (*^)
--   (^+^)   = liftL2 (^+^)
--   negateV = fmapL  negateV

-- Alternatively, add some methods to 'LMapDom' and use them as follows.
-- May be more efficient.

-- -- Linear maps form a vector space
-- instance (VectorSpace o s, LinearMap a o s) => VectorSpace (a :--> o) s where
--   zeroV   = zeroL
--   (^+^)   = addL
--   (*^)    = scaleL
--   negateV = negateL



--- Instances of LMapDom

instance LMapDom Float Float where
  data Float :-* v  = FloatL v
  ($*) (FloatL v)   = (*^ v)
  linear f          = FloatL (f 1)

instance LMapDom Double Double where
  data Double :-* v = DoubleL v
  ($*) (DoubleL v)  = (*^ v)
  linear f          = DoubleL (f 1)


-- | Convenience function for 'linear' definitions.  Both functions are
-- assumed linear.
linearK :: (LMapDom a s) => (a -> b) -> (b -> c) -> a :-* c
linearK k f = linear (f . k)

instance (LMapDom a s, LMapDom b s) => LMapDom (a,b) s where
  data (a,b) :-* o = PairL (a :-* o) (b :-* o)
  PairL ao bo $* (a,b) = ao $* a ^+^ bo $* b
  linear = liftA2 PairL
             (linearK (\ a -> (a,zeroV)))
             (linearK (\ b -> (zeroV,b)))

instance (LMapDom a s, LMapDom b s, LMapDom c s) => LMapDom (a,b,c) s where
  data (a,b,c) :-* o = TripleL (a :-* o) (b :-* o) (c :-* o)
  TripleL ao bo co $* (a,b,c) =
    ao $* a ^+^ bo $* b ^+^ co $* c
  linear = liftA3 TripleL
             (linearK (\ a -> (a,zeroV,zeroV)))
             (linearK (\ b -> (zeroV,b,zeroV)))
             (linearK (\ c -> (zeroV,zeroV,c)))




-- TODO: unfst, unsnd, pair, unpair


---- OpenGL stuff.

-- I'd rather this code be in a different package.  It's here as a
-- temporary bug workaround.  In ghc-6.8.2, I get the following error
-- message if the 'LMapDom' instance (below) is compiled in a separate
-- module.
-- 
--     Type indexes must match class instance head
--     Found o but expected Vector2 u
--     In the associated type instance for `:-*'
--     In the instance declaration for `LMapDom (Vector2 u) s'



-- TODO: is UndecidableInstances still necessary?

instance AdditiveGroup u => AdditiveGroup (Vector2 u) where
  zeroV                         = Vector2 zeroV zeroV
  Vector2 u v ^+^ Vector2 u' v' = Vector2 (u^+^u') (v^+^v')
  negateV (Vector2 u v)         = Vector2 (negateV u) (negateV v)

instance (VectorSpace u s) => VectorSpace (Vector2 u) s where
  s *^ Vector2 u v            = Vector2 (s*^u) (s*^v)

instance (InnerSpace u s, AdditiveGroup s)
    => InnerSpace (Vector2 u) s where
  Vector2 u v <.> Vector2 u' v' = u<.>u' ^+^ v<.>v'

instance LMapDom u s => LMapDom (Vector2 u) s where
  data Vector2 u :-* o = VecL (u :-* o) (u :-* o)
  VecL ao bo $* Vector2 a b = ao $* a ^+^ bo $* b
  linear = liftA2 VecL
             (linearK (\ a -> Vector2 a zeroV))
             (linearK (\ b -> Vector2 zeroV b))



instance AdditiveGroup u => AdditiveGroup (Vector3 u) where
  zeroV                   = Vector3 zeroV zeroV zeroV
  Vector3 u v w ^+^ Vector3 u' v' w'
                          = Vector3 (u^+^u') (v^+^v') (w^+^w')
  negateV (Vector3 u v w) = Vector3 (negateV u) (negateV v) (negateV w)

instance VectorSpace u s => VectorSpace (Vector3 u) s where
  s *^ Vector3 u v w    = Vector3 (s*^u) (s*^v) (s*^w)

instance (InnerSpace u s, AdditiveGroup s)
    => InnerSpace (Vector3 u) s where
  Vector3 u v w <.> Vector3 u' v' w' = u<.>u' ^+^ v<.>v' ^+^ w<.>w'

