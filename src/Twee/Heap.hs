{-# LANGUAGE BangPatterns #-}
-- Skew heaps.
module Twee.Heap(
  Heap, empty, insert, removeMin, fromList, mapMaybe, size) where

data Heap a = Heap {-# UNPACK #-} !Int !(Heap1 a)
data Heap1 a = Nil | Node !a !(Heap1 a) !(Heap1 a)

{-# INLINE merge #-}
merge :: Ord a => Heap a -> Heap a -> Heap a
merge (Heap n1 h1) (Heap n2 h2) = Heap (n1+n2) (merge1 h1 h2)

{-# INLINEABLE merge1 #-}
merge1 :: Ord a => Heap1 a -> Heap1 a -> Heap1 a
merge1 Nil h = h
merge1 h Nil = h
merge1 h1@(Node x1 l1 r1) h2@(Node x2 l2 r2)
  | x1 <= x2 = Node x1 (merge1 r1 h2) l1
  | otherwise = Node x2 (merge1 r2 h1) l2

unit :: a -> Heap a
unit x = Heap 1 (Node x Nil Nil)

empty :: Heap a
empty = Heap 0 Nil

{-# INLINEABLE insert #-}
insert :: Ord a => a -> Heap a -> Heap a
insert x h = merge (unit x) h

{-# INLINEABLE removeMin #-}
removeMin :: Ord a => Heap a -> Maybe (a, Heap a)
removeMin (Heap _ Nil) = Nothing
removeMin (Heap n (Node x l r)) = Just (x, Heap (n-1) (merge1 l r))

{-# INLINEABLE mapMaybe #-}
mapMaybe :: Ord b => (a -> Maybe b) -> Heap a -> Heap b
mapMaybe f (Heap _ h) = fromList (go h [])
  where
    go Nil xs = xs
    go (Node x l r) xs =
      case f x of
        Just !y -> y:go l (go r xs)
        Nothing -> go l (go r xs)

{-# INLINEABLE fromList #-}
fromList :: Ord a => [a] -> Heap a
fromList = mergeMany . map unit 

{-# INLINEABLE mergeMany #-}
mergeMany :: Ord a => [Heap a] -> Heap a
mergeMany [] = empty
mergeMany [h] = h
mergeMany hs = mergeMany (mergePairs hs)
  where
    mergePairs (x:y:xs) = ((:) $! merge x y) $ mergePairs xs
    mergePairs xs = xs

{-# INLINE size #-}
size :: Heap a -> Int
size (Heap n _) = n
