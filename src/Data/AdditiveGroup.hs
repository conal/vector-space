{-# LANGUAGE TypeOperators, CPP #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE ScopedTypeVariables #-}
----------------------------------------------------------------------
-- |
-- Module      :   Data.AdditiveGroup
-- Copyright   :  (c) Conal Elliott and Andy J Gill 2008
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net, andygill@ku.edu
-- Stability   :  experimental
--
-- Groups: zero, addition, and negation (additive inverse)
----------------------------------------------------------------------

module Data.AdditiveGroup
  (
    AdditiveGroup(..), sumV
  , Sum(..), inSum, inSum2
  ) where

import Prelude hiding (foldr)

import Control.Applicative
#if !(MIN_VERSION_base(4,8,0))
import Data.Monoid (Monoid(..))
import Data.Foldable (Foldable)
#endif
import Data.Foldable (foldr)
import Data.Complex hiding (magnitude)
import Data.Ratio
#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup (Semigroup(..))
#endif
import Foreign.C.Types (CSChar, CInt, CShort, CLong, CLLong, CIntMax, CFloat, CDouble)

import Data.MemoTrie

import Data.VectorSpace.Generic
import qualified GHC.Generics as Gnrx
import GHC.Generics (Generic, (:*:)(..))

infixl 6 ^+^, ^-^

-- | Additive group @v@.
class AdditiveGroup v where
  -- | The zero element: identity for '(^+^)'
  zeroV :: v
  default zeroV :: (Generic v, AdditiveGroup (VRep v)) => v
  zeroV = Gnrx.to (zeroV :: VRep v)
  {-# INLINE zeroV #-}
  -- | Add vectors
  (^+^) :: v -> v -> v
  default (^+^) :: (Generic v, AdditiveGroup (VRep v)) => v -> v -> v
  v ^+^ v' = Gnrx.to (Gnrx.from v ^+^ Gnrx.from v' :: VRep v)
  {-# INLINE (^+^) #-}
  -- | Additive inverse
  negateV :: v -> v
  default negateV :: (Generic v, AdditiveGroup (VRep v)) => v -> v
  negateV v = Gnrx.to (negateV $ Gnrx.from v :: VRep v)
  {-# INLINE negateV #-}
  -- | Group subtraction
  (^-^) :: v -> v -> v
  v ^-^ v' = v ^+^ negateV v'

-- | Sum over several vectors
sumV :: (Foldable f, AdditiveGroup v) => f v -> v
sumV = foldr (^+^) zeroV
{-# INLINE sumV #-}

instance AdditiveGroup () where
  zeroV     = ()
  () ^+^ () = ()
  negateV   = id

-- For 'Num' types:
--
-- instance AdditiveGroup n where {zeroV=0; (^+^) = (+); negateV = negate}

#define ScalarTypeCon(con,t) \
  instance con => AdditiveGroup (t) where {zeroV=0; (^+^) = (+); negateV = negate}

#define ScalarType(t) ScalarTypeCon((),t)

ScalarType(Int)
ScalarType(Integer)
ScalarType(Float)
ScalarType(Double)
ScalarType(CSChar)
ScalarType(CInt)
ScalarType(CShort)
ScalarType(CLong)
ScalarType(CLLong)
ScalarType(CIntMax)
ScalarType(CFloat)
ScalarType(CDouble)
ScalarTypeCon(Integral a,Ratio a)

instance (RealFloat v, AdditiveGroup v) => AdditiveGroup (Complex v) where
  zeroV   = zeroV :+ zeroV
  (^+^)   = (+)
  negateV = negate

-- Hm.  The 'RealFloat' constraint is unfortunate here.  It's due to a
-- questionable decision to place 'RealFloat' into the definition of the
-- 'Complex' /type/, rather than in functions and instances as needed.

instance (AdditiveGroup u,AdditiveGroup v) => AdditiveGroup (u,v) where
  zeroV             = (zeroV,zeroV)
  (u,v) ^+^ (u',v') = (u^+^u',v^+^v')
  negateV (u,v)     = (negateV u,negateV v)

instance (AdditiveGroup u,AdditiveGroup v,AdditiveGroup w)
    => AdditiveGroup (u,v,w) where
  zeroV                  = (zeroV,zeroV,zeroV)
  (u,v,w) ^+^ (u',v',w') = (u^+^u',v^+^v',w^+^w')
  negateV (u,v,w)        = (negateV u,negateV v,negateV w)

instance (AdditiveGroup u,AdditiveGroup v,AdditiveGroup w,AdditiveGroup x)
    => AdditiveGroup (u,v,w,x) where
  zeroV                       = (zeroV,zeroV,zeroV,zeroV)
  (u,v,w,x) ^+^ (u',v',w',x') = (u^+^u',v^+^v',w^+^w',x^+^x')
  negateV (u,v,w,x)           = (negateV u,negateV v,negateV w,negateV x)


-- Standard instance for an applicative functor applied to a vector space.
instance AdditiveGroup v => AdditiveGroup (a -> v) where
  zeroV   = pure   zeroV
  (^+^)   = liftA2 (^+^)
  negateV = fmap   negateV


-- Maybe is handled like the Maybe-of-Sum monoid
instance AdditiveGroup a => AdditiveGroup (Maybe a) where
  zeroV = Nothing
  Nothing ^+^ b'      = b'
  a' ^+^ Nothing      = a'
  Just a' ^+^ Just b' = Just (a' ^+^ b')
  negateV = fmap negateV

{-

Alexey Khudyakov wrote:

  I looked through vector-space package and found lawless instance. Namely Maybe's AdditiveGroup instance

  It's group so following relation is expected to hold. Otherwise it's not a group.
  > x ^+^ negateV x == zeroV

  Here is counterexample:

  > let x = Just 2 in x ^+^ negateV x == zeroV
  False

  I think it's not possible to sensibly define group instance for
  Maybe a at all.


I see that the problem here is in distinguishing 'Just zeroV' from
Nothing. I could fix the Just + Just line to use Nothing instead of Just
zeroV when a' ^+^ b' == zeroV, although doing so would require Eq a and
hence lose some generality. Even so, the abstraction leak would probably
show up elsewhere.

Hm.

-}




-- Memo tries
instance (HasTrie u, AdditiveGroup v) => AdditiveGroup (u :->: v) where
  zeroV   = pure   zeroV
  (^+^)   = liftA2 (^+^)
  negateV = fmap   negateV


-- | Monoid under group addition.  Alternative to the @Sum@ in
-- "Data.Monoid", which uses 'Num' instead of 'AdditiveGroup'.
newtype Sum a = Sum { getSum :: a }
  deriving (Eq, Ord, Read, Show, Bounded)

instance Functor Sum where
  fmap f (Sum a) = Sum (f a)
  {-# INLINE fmap #-}

-- instance Applicative Sum where
--   pure a = Sum a
--   Sum f <*> Sum x = Sum (f x)

instance Applicative Sum where
  pure  = Sum
  {-# INLINE pure #-}
  (<*>) = inSum2 ($)
  {-# INLINE (<*>) #-}

instance AdditiveGroup a => Semigroup (Sum a) where
  (<>) = liftA2 (^+^)
  {-# INLINE (<>) #-}

instance AdditiveGroup a => Monoid (Sum a) where
  mempty  = Sum zeroV
#if !(MIN_VERSION_base(4,11,0))
  mappend = (<>)
#endif

-- | Application a unary function inside a 'Sum'
inSum :: (a -> b) -> (Sum a -> Sum b)
inSum = getSum ~> Sum
{-# INLINE inSum #-}

-- | Application a binary function inside a 'Sum'
inSum2 :: (a -> b -> c) -> (Sum a -> Sum b -> Sum c)
inSum2 = getSum ~> inSum
{-# INLINE inSum2 #-}

instance AdditiveGroup a => AdditiveGroup (Sum a) where
  zeroV   = Sum zeroV
  (^+^)   = (<>)
  negateV = inSum negateV

---- to go elsewhere

(~>) :: (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(i ~> o) f = o . f . i
{-# INLINE (~>) #-}

-- result :: (b -> b') -> ((a -> b) -> (a -> b'))
-- result = (.)

-- argument :: (a' -> a) -> ((a -> b) -> (a' -> b))
-- argument = flip (.)

-- g ~> f = result g . argument f



instance AdditiveGroup a => AdditiveGroup (Gnrx.Rec0 a s) where
  zeroV = Gnrx.K1 zeroV
  {-# INLINE zeroV #-}
  negateV (Gnrx.K1 v) = Gnrx.K1 $ negateV v
  {-# INLINE negateV #-}
  Gnrx.K1 v ^+^ Gnrx.K1 w = Gnrx.K1 $ v ^+^ w
  {-# INLINE (^+^) #-}
  Gnrx.K1 v ^-^ Gnrx.K1 w = Gnrx.K1 $ v ^-^ w
  {-# INLINE (^-^) #-}
instance AdditiveGroup (f p) => AdditiveGroup (Gnrx.M1 i c f p) where
  zeroV = Gnrx.M1 zeroV
  {-# INLINE zeroV #-}
  negateV (Gnrx.M1 v) = Gnrx.M1 $ negateV v
  {-# INLINE negateV #-}
  Gnrx.M1 v ^+^ Gnrx.M1 w = Gnrx.M1 $ v ^+^ w
  {-# INLINE (^+^) #-}
  Gnrx.M1 v ^-^ Gnrx.M1 w = Gnrx.M1 $ v ^-^ w
  {-# INLINE (^-^) #-}
instance (AdditiveGroup (f p), AdditiveGroup (g p)) => AdditiveGroup ((f :*: g) p) where
  zeroV = zeroV :*: zeroV
  {-# INLINE zeroV #-}
  negateV (x:*:y) = negateV x :*: negateV y
  {-# INLINE negateV #-}
  (x:*:y) ^+^ (ξ:*:υ) = (x^+^ξ) :*: (y^+^υ)
  {-# INLINE (^+^) #-}
  (x:*:y) ^-^ (ξ:*:υ) = (x^-^ξ) :*: (y^-^υ)
  {-# INLINE (^-^) #-}
