{-# LANGUAGE TypeOperators #-}
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
    AdditiveGroup(..), (^-^), sumV
  ) where

import Control.Applicative
import Data.Complex hiding (magnitude)

import Data.MemoTrie

infixl 6 ^+^, ^-^

-- | Additive group @v@.
class AdditiveGroup v where
  -- | The zero element: identity for '(^+^)'
  zeroV :: v
  -- | Add vectors
  (^+^) :: v -> v -> v
  -- | Additive inverse
  negateV :: v -> v

-- | Group subtraction
(^-^) :: AdditiveGroup v => v -> v -> v
v ^-^ v' = v ^+^ negateV v'

-- | Sum over several vectors
sumV :: AdditiveGroup v => [v] -> v
sumV = foldr (^+^) zeroV

instance AdditiveGroup Double where
  zeroV   = 0.0
  (^+^)   = (+)
  negateV = negate

instance AdditiveGroup Float where
  zeroV   = 0.0
  (^+^)   = (+)
  negateV = negate

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
  negateV (u,v)     = (negateV u, negateV v)

instance (AdditiveGroup u,AdditiveGroup v,AdditiveGroup w)
    => AdditiveGroup (u,v,w) where
  zeroV                  = (zeroV,zeroV,zeroV)
  (u,v,w) ^+^ (u',v',w') = (u^+^u',v^+^v',w^+^w')
  negateV (u,v,w)        = (negateV u, negateV v, negateV w)


-- Standard instance for an applicative functor applied to a vector space.
instance AdditiveGroup v => AdditiveGroup (u->v) where
  zeroV   = pure   zeroV
  (^+^)   = liftA2 (^+^)
  negateV = fmap   negateV

-- Memo tries
instance (HasTrie u, AdditiveGroup v) => AdditiveGroup (u :->: v) where
  zeroV   = pure   zeroV
  (^+^)   = liftA2 (^+^)
  negateV = fmap   negateV
