-- Term indexing, where the inserted values can be given categories.
{-# LANGUAGE CPP, TypeFamilies, ScopedTypeVariables #-}
module KBC.Indexes where

#include "errors.h"
import KBC.Base hiding (empty)
import qualified KBC.Index as Index
import KBC.Index(Index)
import Data.Array
import Data.Maybe

class Rated a where
  rating :: a -> Int
  maxRating :: a -> Int

newtype Indexes a =
  Indexes {
    unIndexes :: Array Int (Index a) }
  deriving Show

{-# INLINE empty #-}
empty :: forall a. Rated a => Indexes a
empty = Indexes (listArray (0, maxRating (undefined :: a)) (repeat Index.Nil))

{-# INLINE singleton #-}
singleton :: (Symbolic a, Rated a) => a -> Indexes a
singleton x = insert x empty

{-# INLINE insert #-}
insert :: forall a. (Symbolic a, Rated a) => a -> Indexes a -> Indexes a
insert x (Indexes idxs) =
  Indexes (idxs // [(i, Index.insert x (idxs ! i)) | i <- [rating x..maxRating (undefined :: a)]])

{-# INLINE delete #-}
delete :: forall a. (Eq a, Symbolic a, Rated a) => a -> Indexes a -> Indexes a
delete x (Indexes idxs) =
  Indexes (idxs // [(i, Index.delete x (idxs ! i)) | i <- [rating x..maxRating (undefined :: a)]])

{-# INLINE freeze #-}
freeze :: Int -> Indexes a -> Index.Frozen a
freeze n (Indexes idxs) = Index.freeze (idxs ! n)

{-# INLINE elems #-}
elems :: forall a. Rated a => Indexes a -> [a]
elems (Indexes idxs) = Index.elems (idxs ! maxRating (undefined :: a))
