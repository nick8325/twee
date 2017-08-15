{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
-- Skew heaps.
module Twee.Heap(
  Heap, empty, insert, removeMin, mapMaybe, size) where

data Heap a = Heap {-# UNPACK #-} !Int !(Heap1 a)
data Heap1 a = Nil | Node a (Heap1 a) (Heap1 a)

{-# INLINEABLE merge #-}
merge :: Ord a => Heap a -> Heap a -> Heap a
merge (Heap n1 h1) (Heap n2 h2) = Heap (n1+n2) (merge1 h1 h2)

{-# INLINEABLE merge1 #-}
merge1 :: forall a. Ord a => Heap1 a -> Heap1 a -> Heap1 a
merge1 = m1
  where
    -- For some reason using m1 improves the code generation...
    m1 :: Heap1 a -> Heap1 a -> Heap1 a
    m1 Nil h = h
    m1 h Nil = h
    m1 h1@(Node x1 l1 r1) h2@(Node x2 l2 r2)
      | x1 <= x2 = (Node x1 $! m1 r1 h2) l1
      | otherwise = (Node x2 $! m1 r2 h1) l2

{-# INLINE unit #-}
unit :: a -> Heap a
unit !x = Heap 1 (Node x Nil Nil)

{-# INLINE empty #-}
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
mapMaybe f (Heap _ h) = Heap (sz 0 h') h'
  where
    sz !n Nil = n
    sz !n (Node _ l r) = sz (sz (n+1) l) r

    h' = go h

    go Nil = Nil
    go (Node x l r) =
      case f x of
        Nothing -> merge1 l' r'
        Just !y -> down y l' r'
      where
        !l' = go l
        !r' = go r

    down x l@(Node y ll lr) r@(Node z rl rr)
      | y < x && y <= z =
        (Node y $! down x ll lr) r
      | z < x && z <= y =
        Node z l $! down x rl rr
    down x Nil (Node y l r)
      | y < x =
        Node y Nil $! down x l r
    down x (Node y l r) Nil
      | y < x =
        (Node y $! down x l r) Nil
    down x l r = Node x l r

{-# INLINE size #-}
size :: Heap a -> Int
size (Heap n _) = n
