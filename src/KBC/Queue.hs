-- A priority queue, with orphan murder.
{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, DeriveFunctor, RecordWildCards #-}
module KBC.Queue where

import KBC.Base
import Data.Ord
import qualified Data.Heap as Heap
import Data.Heap(Heap)
import qualified Data.Set as Set
import Data.Set(Set)

data Queue a =
  Queue {
    queue       :: !(Heap a),
    queueLabels :: Set Label,
    nextLabel   :: Label }
  deriving Show

class Ord a => Labels a where
  labels :: a -> [Label]

getMin :: Heap a -> Maybe a
getMin h
  | Heap.null h = Nothing
  | otherwise = Just (Heap.minimum h)

empty :: Queue q
empty = Queue Heap.empty (Set.singleton noLabel) (noLabel+1)

emptyFrom :: Queue a -> Queue a
emptyFrom q = q { queue = Heap.empty }

enqueue :: Labels a => a -> Queue a -> Queue a
enqueue x q = q { queue = Heap.insert x (queue q) }

dequeue :: Labels a => Queue a -> Maybe (a, Queue a)
dequeue q@Queue{queueLabels = ls, queue = q0} = aux q0
  where
    aux q0 = do
      (x, q1) <- Heap.viewMin q0
      if or [ l `Set.notMember` ls | l <- labels x ] then
        aux q1
      else return (x, q { queue = q1 })

queueSize :: Labels a => Queue a -> Int
queueSize q = length (toList q)

toList :: Labels a => Queue a -> [a]
toList Queue{..} = filter p (Heap.toUnsortedList queue)
  where
    p x = and [ l `Set.member` queueLabels | l <- labels x ]

newtype Label = Label Int deriving (Eq, Ord, Num, Show, Integral, Enum, Real)

noLabel :: Label
noLabel = 0

newLabel :: Queue a -> (Label, Queue a)
newLabel q@Queue{nextLabel = n, queueLabels = ls} =
  (n, q { nextLabel = n+1, queueLabels = Set.insert n ls } )

deleteLabel :: Label -> Queue a -> Queue a
deleteLabel l q@Queue{queueLabels = ls} = q { queueLabels = Set.delete l ls }

data Labelled a = Labelled { labelOf :: Label, peel :: a } deriving (Show, Functor)

instance Eq a => Eq (Labelled a) where x == y = peel x == peel y
instance Ord a => Ord (Labelled a) where compare = comparing peel
instance Symbolic a => Symbolic (Labelled a) where
  type ConstantOf (Labelled a) = ConstantOf a
  termListsDL = termListsDL . peel
  subst sub (Labelled l x) = Labelled l (subst sub x)
instance Pretty a => Pretty (Labelled a) where pPrint = pPrint . peel

moveLabel :: Functor f => Labelled (f a) -> f (Labelled a)
moveLabel (Labelled l x) = fmap (Labelled l) x

unlabelled :: a -> Labelled a
unlabelled = Labelled noLabel

