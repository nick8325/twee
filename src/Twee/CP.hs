-- Critical pairs.
{-# LANGUAGE BangPatterns, CPP #-}
module Twee.CP where

#include "errors.h"
import Twee.Base
import Twee.Rule
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe
import qualified Data.DList as DList

-- The set of positions at which a term can have critical overlaps.
newtype Positions f = Positions [Int]

positions :: Term f -> Positions f
positions t = Positions (aux 0 Set.empty (singleton t))
  where
    aux !_ !_ Empty = []
    aux n m (Cons (Var _) t) = aux (n+1) m t
    aux n m (ConsSym t@App{} u)
      | t `Set.member` m = aux (n+1) m u
      | otherwise = n:aux (n+1) (Set.insert t m) u

-- A critical overlap of one term with another.
data Overlap f =
  Overlap {
    overlap_top      :: {-# UNPACK #-} !(Term f),
    overlap_left     :: {-# UNPACK #-} !(Term f),
    overlap_right    :: {-# UNPACK #-} !(Term f),
    overlap_inner    :: {-# UNPACK #-} !(Term f) }

-- Compute all overlaps of two rules. They should have no
-- variables in common.
overlaps1 :: Positions f -> Rule f -> Rule f -> [Overlap f]
overlaps1 (Positions ns) (Rule _ !outer !outer') (Rule _ !inner !inner') = do
  n <- ns
  let t = at n (singleton outer)
  sub <- maybeToList (unify inner t)
  let top = subst sub outer
      left = subst sub outer'
      right = build (replacePositionSub (evalSubst sub) n (singleton inner') (singleton outer))
      inner_ = subst sub inner
  return (Overlap top left right inner_)

-- Compute all overlaps of a rule with a set of rules.
overlaps :: IntMap (Rule f) -> Rule f -> [Overlap f]
overlaps = undefined
