-- | Skew heaps.

{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
module Data.Heap(
  Heap, empty, singleton, insert, removeMin, union, mapMaybe, size) where

-- | A heap.

-- Representation: the size of the heap, and the heap itself.
data Heap a = Heap {-# UNPACK #-} !Int !(Heap1 a) deriving Show
-- N.B.: arguments are not strict so code has to take care
-- to force stuff appropriately.
data Heap1 a = Nil | Node a (Heap1 a) (Heap1 a) deriving Show

-- | Take the union of two heaps.
{-# INLINEABLE union #-}
union :: Ord a => Heap a -> Heap a -> Heap a
union (Heap n1 h1) (Heap n2 h2) = Heap (n1+n2) (union1 h1 h2)

{-# INLINEABLE union1 #-}
union1 :: forall a. Ord a => Heap1 a -> Heap1 a -> Heap1 a
union1 = u1
  where
    -- The generated code is better when we do everything
    -- through this u1 function instead of union1...
    -- This is because u1 has no Ord constraint in its type.
    u1 :: Heap1 a -> Heap1 a -> Heap1 a
    u1 Nil h = h
    u1 h Nil = h
    u1 h1@(Node x1 l1 r1) h2@(Node x2 l2 r2)
      | x1 <= x2 = (Node x1 $! u1 r1 h2) l1
      | otherwise = (Node x2 $! u1 r2 h1) l2

-- | A singleton heap.
{-# INLINE singleton #-}
singleton :: a -> Heap a
singleton !x = Heap 1 (Node x Nil Nil)

-- | The empty heap.
{-# INLINE empty #-}
empty :: Heap a
empty = Heap 0 Nil

-- | Insert an element.
{-# INLINEABLE insert #-}
insert :: Ord a => a -> Heap a -> Heap a
insert x h = union (singleton x) h

-- | Find and remove the minimum element.
{-# INLINEABLE removeMin #-}
removeMin :: Ord a => Heap a -> Maybe (a, Heap a)
removeMin (Heap _ Nil) = Nothing
removeMin (Heap n (Node x l r)) = Just (x, Heap (n-1) (union1 l r))

-- | Map a function over a heap, removing all values which
-- map to 'Nothing'. May be more efficient when the function
-- being mapped is mostly monotonic.
{-# INLINEABLE mapMaybe #-}
mapMaybe :: Ord b => (a -> Maybe b) -> Heap a -> Heap b
mapMaybe f (Heap _ h) = Heap (sz 0 h') h'
  where
    -- Compute the size fairly efficiently.
    sz !n Nil = n
    sz !n (Node _ l r) = sz (sz (n+1) l) r

    h' = mm h

    mm Nil = Nil
    mm (Node x l r) =
      case f x of
        -- If the value maps to Nothing, get rid of it.
        Nothing -> union1 l' r'
        -- Otherwise, check if the heap invariant still holds
        -- and sift downwards to restore it.
        Just !y -> down y l' r'
      where
        !l' = mm l
        !r' = mm r

    down x l@(Node y ll lr) r@(Node z rl rr)
      -- Put the smallest of x, y and z at the root.
      | y < x && y <= z =
        (Node y $! down x ll lr) r
      | z < x && z <= y =
        Node z l $! down x rl rr
    down x Nil (Node y l r)
      -- Put the smallest of x and y at the root.
      | y < x =
        Node y Nil $! down x l r
    down x (Node y l r) Nil
      -- Put the smallest of x and y at the root.
      | y < x =
        (Node y $! down x l r) Nil
    down x l r = Node x l r

-- | Return the number of elements in the heap.
{-# INLINE size #-}
size :: Heap a -> Int
size (Heap n _) = n

-- Testing code:
-- import Test.QuickCheck
-- import qualified Data.List as List
-- import qualified Data.Maybe as Maybe

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

-- toList :: Ord a => Heap a -> [a]
-- toList = List.unfoldr removeMin

-- invariant :: Ord a => Heap a -> Bool
-- invariant h@(Heap n h1) =
--   n == length (toList h) && ord h1
--   where
--     ord Nil = True
--     ord (Node x l r) = ord1 x l && ord1 x r

--     ord1 _ Nil = True
--     ord1 x h@(Node y _ _) = x <= y && ord h

-- prop_1 h = withMaxSuccess 10000 $ invariant h
-- prop_2 x h = withMaxSuccess 10000 $ invariant (insert x h)
-- prop_3 h =
--   withMaxSuccess 1000 $
--   case removeMin h of
--     Nothing -> discard
--     Just (_, h) -> invariant h
-- prop_4 h = withMaxSuccess 10000 $ List.sort (toList h) == toList h
-- prop_5 x h = withMaxSuccess 10000 $ toList (insert x h) == List.insert x (toList h)
-- prop_6 x h =
--   withMaxSuccess 1000 $
--   case removeMin h of
--     Nothing -> discard
--     Just (x, h') -> toList h == List.insert x (toList h')
-- prop_7 h1 h2 = withMaxSuccess 10000 $
--   invariant (union h1 h2)
-- prop_8 h1 h2 = withMaxSuccess 10000 $
--   toList (union h1 h2) == List.sort (toList h1 ++ toList h2)
-- prop_9 (Blind f) h = withMaxSuccess 10000 $
--   invariant (mapMaybe f h)
-- prop_10 (Blind f) h = withMaxSuccess 1000000 $
--   toList (mapMaybe f h) == List.sort (Maybe.mapMaybe f (toList h))

-- return []
-- main = $quickCheckAll
