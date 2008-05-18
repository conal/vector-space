{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.NumInstances
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Number class instances for functions and tuples
----------------------------------------------------------------------

module Data.NumInstances () where

import Control.Applicative

noOv :: String -> String -> a
noOv ty meth = error $ meth ++ ": No overloading for " ++ ty

noFun :: String -> a
noFun = noOv "function"

-- Eq & Show are prerequisites for Num, so they need to be faked here
instance Eq (a->b) where
  (==) = noFun "(==)"
  (/=) = noFun "(/=)"

instance Ord b => Ord (a->b) where
  min = liftA2 min
  max = liftA2 max

instance Show (a->b) where
  show      = noFun "show"
  showsPrec = noFun "showsPrec"
  showList  = noFun "showList"

instance Num b => Num (a->b) where
  negate      = fmap negate
  (+)         = liftA2 (+)
  (*)         = liftA2 (*)
  fromInteger = pure . fromInteger
  abs         = fmap abs
  signum      = fmap signum

instance Fractional b => Fractional (a->b) where
  recip        = fmap recip
  fromRational = pure . fromRational

instance Floating b => Floating (a->b) where
  pi    = pure pi
  sqrt  = fmap sqrt
  exp   = fmap exp
  log   = fmap log
  sin   = fmap sin
  cos   = fmap cos
  asin  = fmap asin
  atan  = fmap atan
  acos  = fmap acos
  sinh  = fmap sinh
  cosh  = fmap cosh
  asinh = fmap asinh
  atanh = fmap atanh
  acosh = fmap acosh


----- Tuples

lift2 :: (a->u) -> (b->v) -> (a,b) -> (u,v)
lift2 f g (a,b) = (f a, g b)

instance (Num a, Num b) => Num (a,b) where
  fromInteger n   = (fromInteger n, fromInteger n)
  (a,b) + (a',b') = (a+a',b+b')
  (a,b) - (a',b') = (a-a',b-b')
  (a,b) * (a',b') = (a*a',b*b')
  negate = lift2 negate negate
  abs    = lift2 abs abs
  signum = lift2 signum signum

instance (Fractional a, Fractional b) => Fractional (a,b) where
  fromRational x = (fromRational x, fromRational x)
  recip = lift2 recip recip

instance (Floating a, Floating b) => Floating (a,b) where
  pi    = (pi,pi)
  exp   = lift2 exp exp
  log   = lift2 log log
  sqrt  = lift2 sqrt sqrt
  sin   = lift2 sin sin
  cos   = lift2 cos cos
  sinh  = lift2 sinh sinh
  cosh  = lift2 cosh cosh
  asin  = lift2 asin asin
  acos  = lift2 acos acos
  atan  = lift2 atan atan
  asinh = lift2 asinh asinh
  acosh = lift2 acosh acosh
  atanh = lift2 atanh atanh

instance (Num a, Num b, Num c) => Num (a,b,c) where
  fromInteger n = (fromInteger n, fromInteger n, fromInteger n)
  (a,b,c) + (a',b',c') = (a+a',b+b',c+c')
  (a,b,c) - (a',b',c') = (a-a',b-b',c-c')
  (a,b,c) * (a',b',c') = (a*a',b*b',c*c')
  negate = lift3 negate negate negate
  abs    = lift3 abs abs abs
  signum = lift3 signum signum signum

instance (Fractional a, Fractional b, Fractional c)
    => Fractional (a,b,c) where
  fromRational x = (fromRational x, fromRational x, fromRational x)
  recip = lift3 recip recip recip


lift3 :: (a->u) -> (b->v) -> (c->w) -> (a,b,c) -> (u,v,w)
lift3 f g h (a,b,c) = (f a, g b, h c)

instance (Floating a, Floating b, Floating c)
    => Floating (a,b,c) where
  pi    = (pi,pi,pi)
  exp   = lift3 exp exp exp
  log   = lift3 log log log
  sqrt  = lift3 sqrt sqrt sqrt
  sin   = lift3 sin sin sin
  cos   = lift3 cos cos cos
  sinh  = lift3 sinh sinh sinh
  cosh  = lift3 cosh cosh cosh
  asin  = lift3 asin asin asin
  acos  = lift3 acos acos acos
  atan  = lift3 atan atan atan
  asinh = lift3 asinh asinh asinh
  acosh = lift3 acosh acosh acosh
  atanh = lift3 atanh atanh atanh



lift4 :: (a->u) -> (b->v) -> (c->w) -> (d->x)
      -> (a,b,c,d) -> (u,v,w,x)
lift4 f g h k (a,b,c,d) = (f a, g b, h c, k d)

instance (Num a, Num b, Num c, Num d) => Num (a,b,c,d) where
  fromInteger n = (fromInteger n, fromInteger n, fromInteger n, fromInteger n)
  (a,b,c,d) + (a',b',c',d') = (a+a',b+b',c+c',d+d')
  (a,b,c,d) - (a',b',c',d') = (a-a',b-b',c-c',d-d')
  (a,b,c,d) * (a',b',c',d') = (a*a',b*b',c*c',d*d')
  negate = lift4 negate negate negate negate
  abs    = lift4 abs abs abs abs
  signum = lift4 signum signum signum signum

instance (Fractional a, Fractional b, Fractional c, Fractional d)
    => Fractional (a,b,c,d) where
  fromRational x = (fromRational x, fromRational x, fromRational x, fromRational x)
  recip = lift4 recip recip recip recip

instance (Floating a, Floating b, Floating c, Floating d)
    => Floating (a,b,c,d) where
  pi    = (pi,pi,pi,pi)
  exp   = lift4 exp exp exp exp
  log   = lift4 log log log log
  sqrt  = lift4 sqrt sqrt sqrt sqrt
  sin   = lift4 sin sin sin sin
  cos   = lift4 cos cos cos cos
  sinh  = lift4 sinh sinh sinh sinh
  cosh  = lift4 cosh cosh cosh cosh
  asin  = lift4 asin asin asin asin
  acos  = lift4 acos acos acos acos
  atan  = lift4 atan atan atan atan
  asinh = lift4 asinh asinh asinh asinh
  acosh = lift4 acosh acosh acosh acosh
  atanh = lift4 atanh atanh atanh atanh
