{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances
           , MultiParamTypeClasses, FlexibleInstances
           , FunctionalDependencies
  #-}
{-# OPTIONS_GHC -fno-warn-orphans -fglasgow-exts #-}
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
    LMapDom(..), inL, inL2
  , linearK, (.*)
  , pureL, (<*>*), fmapL, (<$>*), liftL2, liftL3, idL
  , test1 -- export temporarily, to make sure it gets compiled
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
infixl 4 <*>*, <$>*


-- | Domain of a linear map.
class VectorSpace a s => LMapDom a s | a -> s where
  -- | Linear map type
  data (:-*) a :: * -> *
  -- | Linear map as function
  ($*) :: VectorSpace b s => (a :-* b) -> (a -> b)
  -- | Function (assumed linear) as linear map.
  linear :: (a -> b) -> (a :-* b)


{-# RULES
"linear.($*)"   forall m. linear (($*) m) = m
"($*).linear"   forall f. ($*) (linear f) = f
 #-}

-- Will the rules fire if written as follows?  Would the rewrite engine
-- inline composition in the rules themselves to make them applicable?
-- 
--   {-# RULES
--     "linear.($*)"   linear . ($*) == id
--     "($*).linear"   ($*) . linear == id
--    #-}


-- | Transform a linear map by transforming a linear function.
inL :: (LMapDom c s, VectorSpace b s', LMapDom a s') =>
        ((a -> b) -> (c -> d)) -> ((a :-* b) -> (c :-* d))
inL h = linear . h . ($*)

-- | Transform a linear maps by transforming linear functions.
inL2 :: ( LMapDom c s, VectorSpace b s', LMapDom a s'
         , LMapDom c s''
         , LMapDom e s, VectorSpace d s
         ) =>
         ((a -> b) -> (c -> d) -> (e -> f))
      -> ((a :-* b) -> (c :-* d) -> (e :-* f))
inL2 h = inL . h . ($*)

-- TODO: go through this whole module and relax constraints on scalar
-- fields.  See if it helps with the scalar dilemma in Mac2


-- | Constant value as a linear map
pureL :: LMapDom a s => b -> (a :-* b)
pureL b = linear (const b)

-- | Like '(<*>)' for linear maps.
(<*>*) :: (LMapDom a s, VectorSpace b s, VectorSpace c s) =>
        (a :-* (b -> c)) -> (a :-* b) -> (a :-* c)
(<*>*) = inL2 (<*>)

-- | Map a /linear/ function over a linear map.
fmapL, (<$>*) :: (LMapDom a s, VectorSpace b s) =>
                 (b -> c) -> (a :-* b) -> (a :-* c)
fmapL f = inL (f .)

-- fmapL f
--   = inL (f .)
--   = linear . (f .) . ($*)
--   = \ m -> linear (f . (($*) m))

(<$>*) = fmapL

{-# INLINE inL #-}
{-# INLINE fmapL #-}

-- If 'fmapL', 'inL' and '(.)' inline in 'test1', then the rule
-- "($*).linear" ought to fire.  Test with -ddump-simpl-stats
test1 :: (VectorSpace b s, LMapDom a s, Num b) => (a :-* b) -> a :-* b
test1 z = fmapL (*3) . fmapL (*4) $ z

-- | Apply a /linear/ binary function over linear maps.
liftL2 :: ( LMapDom a s, VectorSpace b s
           , VectorSpace c s, VectorSpace d s) =>
           (b -> c -> d) -> (a :-* b) -> (a :-* c) -> (a :-* d)

-- liftL2 f b c = fmapL f b <*>* c

liftL2 f b c = linear (liftA2 f (($*) b) (($*) c))

-- I expected the following definition to be equivalent, thanks to rewriting:
-- 
--   liftL2 f b c = fmapL f b <*>* c
--     = linear (f . ($*) b) <*>* c
--     = linear (($*) (linear (f . ($*) b)) <*> ($*) c)
--     = linear ((f . ($*) b) <*> ($*) c)
--     = linear (liftA2 f (($*) b) (($*) c))
-- 
-- Isn't happening, however.  And this simpler definition yields an
-- incredibly slow implementation.
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
--     = linear (liftA2 f (($*) b) (($*) c))           -- uninline liftA2

-- When I compile this module, I don't get any firings of ($*).linear


-- | Apply a /linear/ ternary function over linear maps.
liftL3 :: ( LMapDom a s, VectorSpace b s, VectorSpace c s
           , VectorSpace d s, VectorSpace e s) =>
           (b -> c -> d -> e)
        -> (a :-* b) -> (a :-* c) -> (a :-* d) -> (a :-* e)
liftL3 f b c d = linear (liftA3 f (($*) b) (($*) c) (($*) d))

--   liftL3 f b c d = liftL2 f b c <*>* d


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

