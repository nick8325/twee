-- A priority queue, with orphan murder.
{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, DeriveFunctor, RecordWildCards, BangPatterns #-}
module Twee.Queue(module Twee.Queue, Heap.Heap) where

import Twee.Base
import Data.Ord
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.List as List
import qualified Data.Heap as Heap
import Control.Monad

class Heuristic h where
  insert :: Ord a => a -> h a -> h a
  remove :: Ord a => h a -> Maybe (a, h a)

  reinsert :: Ord a => a -> h a -> h a
  reinsert = insert

  members :: Ord a => h a -> [a]
  members = List.unfoldr remove

instance Heuristic Heap.Heap where
  insert = Heap.insert
  remove = Heap.viewMin
  members = Heap.toUnsortedList

emptyHeap :: Heap.Heap a
emptyHeap = Heap.empty

data FIFO a = FIFO [a] [a] deriving Show

emptyFIFO :: FIFO a
emptyFIFO = FIFO [] []

instance Heuristic FIFO where
  insert x (FIFO xs ys) = FIFO (x:xs) ys
  remove (FIFO [] []) = Nothing
  remove (FIFO xs []) = remove (FIFO [] (reverse xs))
  remove (FIFO xs (y:ys)) = Just (y, FIFO xs ys)

  reinsert x (FIFO xs ys) = FIFO xs (x:ys)
  --members (FIFO xs ys) = ys ++ reverse xs
  members _ = []

data Either1 h1 h2 a = Left1 (h1 a) | Right1 (h2 a) deriving Show

instance (Heuristic h1, Heuristic h2) => Heuristic (Either1 h1 h2) where
  insert x (Left1 q) = Left1 (insert x q)
  insert x (Right1 q) = Right1 (insert x q)
  reinsert x (Left1 q) = Left1 (reinsert x q)
  reinsert x (Right1 q) = Right1 (reinsert x q)
  remove (Left1 q) = fmap (fmap Left1) (remove q)
  remove (Right1 q) = fmap (fmap Right1) (remove q)
  members (Left1 q) = members q
  members (Right1 q) = members q

data Mix h a =
  Mix {
    takeLeft  :: {-# UNPACK #-} !Int,
    takeRight :: {-# UNPACK #-} !Int,
    takeNext  :: {-# UNPACK #-} !Int,
    left      :: !(h a),
    right     :: !(h a) }
  deriving Show

emptyMix :: Int -> Int -> h a -> h a -> Mix h a
emptyMix m n l r = Mix m n m l r

instance Heuristic h => Heuristic (Mix h) where
  insert x mix =
    mix { left = insert x (left mix),
          right = insert x (right mix) }

  remove mix = go mix `mplus` go (swap mix) `mplus` go (reset mix)
    where
      go mix@Mix{..} = do
        guard (takeNext > 0)
        (x, left') <- remove left
        return (x, mix { takeNext = takeNext - 1, left = left' })
      swap Mix{..} = Mix takeRight takeLeft takeRight right left
      reset Mix{..} = Mix takeLeft takeRight takeLeft left right

  reinsert x mix =
    mix { left = reinsert x (left mix),
          right = reinsert x (right mix) }

  members mix =
    members (left mix) ++ members (right mix)

data Queue h a =
  Queue {
    queue       :: !(h a),
    emptyQueue  :: h a,
    queueLabels :: Set Label,
    nextLabel   :: Label }
  deriving Show

class Ord a => Labels a where
  labels :: a -> [Label]

empty :: h a -> Queue h a
empty q = Queue q q (Set.singleton noLabel) (noLabel+1)

emptyFrom :: Queue q a -> Queue q a
emptyFrom q = q { queue = emptyQueue q }

enqueue :: (Heuristic h, Labels a) => a -> Queue h a -> Queue h a
enqueue x q = q { queue = insert x (queue q) }

reenqueue :: (Heuristic h, Labels a) => a -> Queue h a -> Queue h a
reenqueue x q = q { queue = reinsert x (queue q) }

dequeue :: (Heuristic h, Labels a) => Queue h a -> Maybe (a, Queue h a)
dequeue q@Queue{queueLabels = ls, queue = q0} = aux q0
  where
    aux q0 = do
      (x, q1) <- remove q0
      if or [ l `Set.notMember` ls | l <- labels x ] then
        aux q1
      else return (x, q { queue = q1 })

queueSize :: (Heuristic h, Labels a) => Queue h a -> Int
queueSize q = length (toList q)

toList :: (Heuristic h, Labels a) => Queue h a -> [a]
toList Queue{..} = filter p (members queue)
  where
    p x = and [ l `Set.member` queueLabels | l <- labels x ]

newtype Label = Label Int deriving (Eq, Ord, Num, Show, Integral, Enum, Real)

noLabel :: Label
noLabel = 0

newLabel :: Queue h a -> (Label, Queue h a)
newLabel q@Queue{nextLabel = n, queueLabels = ls} =
  (n, q { nextLabel = n+1, queueLabels = Set.insert n ls } )

deleteLabel :: Label -> Queue h a -> Queue h a
deleteLabel l q@Queue{queueLabels = ls} = q { queueLabels = Set.delete l ls }

data Labelled a = Labelled { labelOf :: Label, peel :: a } deriving (Show, Functor)

instance Eq (Labelled a) where x == y = labelOf x == labelOf y
instance Ord (Labelled a) where compare = comparing labelOf
instance Symbolic a => Symbolic (Labelled a) where
  type ConstantOf (Labelled a) = ConstantOf a
  term = term . peel
  termsDL = termsDL . peel
  replace f (Labelled l x) = Labelled l (replace f x)
instance Pretty a => Pretty (Labelled a) where pPrint = pPrint . peel

moveLabel :: Functor f => Labelled (f a) -> f (Labelled a)
moveLabel (Labelled l x) = fmap (Labelled l) x

unlabelled :: a -> Labelled a
unlabelled = Labelled noLabel

