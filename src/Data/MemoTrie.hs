{-# LANGUAGE GADTs, TypeFamilies, TypeOperators #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.MemoTrie
-- Copyright   :  (c) Conal Elliott 2007
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Trie-based memoizer
-- Adapted from sjanssen's paste: "a lazy trie" <http://hpaste.org/3839>.
----------------------------------------------------------------------

module Data.MemoTrie
  ( memo, memo2, memo3, mup, Trie(..)
  , tabulateBits, applyBits
  ) where

import Data.Bits
import Data.Word
import Control.Applicative
import Data.Monoid

-- | Trie-based function memoizer
memo :: Trie t => (t -> a) -> (t -> a)
memo = apply . tabulate

-- | Memoize a binary function, on its first argument and then on its
-- second.  Take care to exploit any partial evaluation.
memo2 :: (Trie s,Trie t) => (s -> t -> a) -> (s -> t -> a)

-- | Memoize a ternary function on successive arguments.  Take care to
-- exploit any partial evaluation.
memo3 :: (Trie r,Trie s,Trie t) => (r -> s -> t -> a) -> (r -> s -> t -> a)

-- | Lift a memoizer to work with one more argument.
mup :: Trie t => (b -> c) -> (t -> b) -> (t -> c)
mup mem f = memo (mem . f)

memo2 = mup memo
memo3 = mup memo2


-- Mapping from all elements of 'a' to the results of some function
class Trie a where
    data (:->:) a :: * -> *
    -- create the table
    tabulate :: (a -> b) -> (a :->: b)
    -- access a field of the table
    apply    :: (a :->: b) -> (a -> b)

{-# RULES
"tabulate/apply"   forall t. tabulate (apply t) = t
"apply/tabulate"   forall f. apply (tabulate f) = f
 #-}


instance Trie Bool where
    data Bool :->: a = BoolTable a a
    tabulate f = BoolTable (f False) (f True)
    apply (BoolTable f _) False = f
    apply (BoolTable _ t) True  = t

instance Trie () where
    data () :->: a = UnitTable a
    tabulate f = UnitTable (f ())
    apply (UnitTable x) () = x

instance (Trie a, Trie b) => Trie (Either a b) where
    data (Either a b) :->: x = EitherTable (a :->: x) (b :->: x)
    apply (EitherTable f _) (Left x) = apply f x
    apply (EitherTable _ g) (Right y) = apply g y
    tabulate f = EitherTable (tabulate (f . Left)) (tabulate (f . Right))

instance (Trie a, Trie b) => Trie (a,b) where
    data (a,b) :->: x = PairTable (a :->: (b :->: x))
    apply (PairTable f) (a,b) = apply (apply f a) b
    tabulate f = PairTable $ tabulate $ \a -> tabulate $ \b -> f (a,b)

instance (Trie a, Trie b, Trie c) => Trie (a,b, c) where
    data (a,b,c) :->: x = TripleTable (a :->: (b :->: (c :->: x)))
    apply (TripleTable f) (a,b,c) = apply (apply (apply f a) b) c
    tabulate f = TripleTable $
      tabulate $ \a -> tabulate $ \b -> tabulate $ \ c -> f (a,b,c)

instance Trie x => Trie [x] where
    data [x] :->: a = ListTable a (x :->: ([x] :->: a))
    tabulate f = ListTable (f []) $ tabulate (\x -> tabulate (f . (x:)))
    apply (ListTable n _) []     = n
    apply (ListTable _ t) (x:xs) = apply (apply t x) xs

-- Handy for Bits types

-- | Extract bits in little-endian order
bits :: Bits t => t -> [Bool]
bits 0 = []
bits x = testBit x 0 : bits (shiftR x 1)

-- | Convert boolean to 0 (False) or 1 (True)
unbit :: Num t => Bool -> t
unbit False = 0
unbit True  = 1

-- | Bit list to value
unbits :: Bits t => [Bool] -> t
unbits [] = 0
unbits (x:xs) = unbit x .|. shiftL (unbits xs) 1

-- | Handy for 'tabulate' in a bits-based 'Trie' instance
tabulateBits :: Bits t => (t -> a) -> ([Bool] :->: a)
tabulateBits f = tabulate (f . unbits)

-- | Handy for 'apply' in a bits-based 'Trie' instance
applyBits :: Bits t => ([Bool] :->: a) -> (t -> a)
applyBits t x = apply t (bits x)

instance Trie Word where
    data Word :->: a = WordTable ([Bool] :->: a)
    apply (WordTable t) = applyBits t
    tabulate = WordTable . tabulateBits

-- Although Int is a Bits instance, we can't use bits directly for
-- memoizing, because the "bits" function gives an infinite result, since
-- shiftR (-1) 1 == -1.  Instead, convert between Int and Word, and use
-- a Word trie.

instance Trie Int where
    data Int :->: a = IntTable (Word :->: a)
    apply (IntTable t) n = apply t (fromIntegral n)
    tabulate f = IntTable (tabulate (f . fromIntegral . toInteger))


---- Instances

{-

'apply' is a 'Functor'-, 'Applicative'-, and 'Monoid'-morphism, i.e.,

  apply (fmap f t)      == fmap f (apply t)

  apply (pure a)        == pure a
  apply (tf <*> tx)     == apply tf <*> apply tx

  apply mempty          == mempty
  apply (s `mappend` t) == apply s `mappend` apply t

The implementation instances then follow from applying 'tabulate' to both
sides of each of these morphism laws.

-}

instance Trie a => Functor ((:->:) a) where
  fmap f t      = tabulate (fmap f (apply t))

instance Trie a => Applicative ((:->:) a) where
  pure b        = tabulate (pure b)
  tf <*> tx     = tabulate (apply tf <*> apply tx)

instance (Trie a, Monoid b) => Monoid (a :->: b) where
  mempty        = tabulate mempty
  s `mappend` t = tabulate (apply s `mappend` apply t)
