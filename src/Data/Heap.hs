-- | Skew heaps.

{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
module Data.Heap(
  Heap, empty, singleton, insert, removeMin, union, mapMaybe, size, toList) where

import qualified Data.List as List

-- | A heap.

-- N.B.: arguments are not strict so code has to take care
-- to force stuff appropriately.
-- The Int field is the size of the heap.
data Heap a = Nil | Node {-# UNPACK #-} !Int a (Heap a) (Heap a) deriving Show

-- | Take the union of two heaps.
{-# INLINEABLE union #-}
union :: forall a. Ord a => Heap a -> Heap a -> Heap a
union = u
  where
    -- The generated code is better when we do everything
    -- through this u function instead of union...
    -- This is because u has no Ord constraint in its type.
    u :: Heap a -> Heap a -> Heap a
    u Nil h = h
    u h Nil = h
    u h1@(Node s1 x1 l1 r1) h2@(Node s2 x2 l2 r2)
      | x1 <= x2 = (Node (s1+s2) x1 $! u r1 h2) l1
      | otherwise = (Node (s1+s2) x2 $! u r2 h1) l2

-- | A singleton heap.
{-# INLINE singleton #-}
singleton :: a -> Heap a
singleton !x = Node 1 x Nil Nil

-- | The empty heap.
{-# INLINE empty #-}
empty :: Heap a
empty = Nil

-- | Insert an element.
{-# INLINEABLE insert #-}
insert :: Ord a => a -> Heap a -> Heap a
insert x h = union (singleton x) h

-- | Find and remove the minimum element.
{-# INLINEABLE removeMin #-}
removeMin :: Ord a => Heap a -> Maybe (a, Heap a)
removeMin Nil = Nothing
removeMin (Node _ x l r) = Just (x, union l r)

-- | Get the elements of a heap as a list, in unspecified order.
toList :: Heap a -> [a]
toList h = tl h []
  where
    tl Nil = id
    tl (Node _ x l r) = (x:) . tl l . tl r

-- | Map a function over a heap, removing all values which
-- map to 'Nothing'. May be more efficient when the function
-- being mapped is mostly monotonic.
{-# INLINEABLE mapMaybe #-}
mapMaybe :: forall a b. Ord b => (a -> Maybe b) -> Heap a -> Heap b
mapMaybe f h = mm h
  where
    mm :: Heap a -> Heap b
    mm Nil = Nil
    mm (Node _ x l r) =
      case f x of
        -- If the value maps to Nothing, get rid of it.
        Nothing -> union l' r'
        -- If y is still the smallest in its subheap,
        -- the calls to insert and union here will work without making
        -- any recursive subcalls!
        Just !y -> insert y l' `union` r'
      where
        !l' = mm l
        !r' = mm r

-- | Return the number of elements in the heap.
{-# INLINE size #-}
size :: Heap a -> Int
size Nil = 0
size (Node n _ _ _) = n

-- Testing code:
-- import Test.QuickCheck
-- import qualified Data.List as List
-- import qualified Data.Maybe as Maybe
-- 
-- instance (Arbitrary a, Ord a) => Arbitrary (Heap a) where
--   arbitrary = sized arb
--     where
--       arb 0 = return empty
--       arb n =
--         frequency
--           [(1, singleton <$> arbitrary),
--            (n-1, union <$> arb' <*> arb')]
--         where
--           arb' = arb (n `div` 2)
-- 
-- toSortedList :: Ord a => Heap a -> [a]
-- toSortedList = List.unfoldr removeMin
-- 
-- invariant :: Ord a => Heap a -> Bool
-- invariant h = ord h && sizeOK h
--   where
--     ord Nil = True
--     ord (Node _ x l r) = ord1 x l && ord1 x r
-- 
--     ord1 _ Nil = True
--     ord1 x h@(Node _ y _ _) = x <= y && ord h
-- 
--     sizeOK Nil = size Nil == 0
--     sizeOK (Node s _ l r) =
--       s == size l + size r + 1
-- 
-- prop_1 h = withMaxSuccess 100000 $ invariant h
-- prop_2 x h = withMaxSuccess 100000 $ invariant (insert x h)
-- prop_3 h =
--   withMaxSuccess 100000 $
--   case removeMin h of
--     Nothing -> discard
--     Just (_, h) -> invariant h
-- prop_4 h = withMaxSuccess 100000 $ List.sort (toSortedList h) == toSortedList h
-- prop_5 x h = withMaxSuccess 100000 $ toSortedList (insert x h) == List.insert x (toSortedList h)
-- prop_6 x h =
--   withMaxSuccess 100000 $
--   case removeMin h of
--     Nothing -> discard
--     Just (x, h') -> toSortedList h == List.insert x (toSortedList h')
-- prop_7 h1 h2 = withMaxSuccess 100000 $
--   invariant (union h1 h2)
-- prop_8 h1 h2 = withMaxSuccess 100000 $
--   toSortedList (union h1 h2) == List.sort (toSortedList h1 ++ toSortedList h2)
-- prop_9 (Blind f) h = withMaxSuccess 100000 $
--   invariant (mapMaybe f h)
-- prop_10 (Blind f) h = withMaxSuccess 1000000 $
--   toSortedList (mapMaybe f h) == List.sort (Maybe.mapMaybe f (toSortedList h))
-- 
-- return []
-- main = $quickCheckAll
