-- Critical pairs.
{-# LANGUAGE BangPatterns, CPP #-}
module Twee.CP where

#include "errors.h"
import Twee.Base
import Twee.Rule
import Twee.Index.Simple(Index)
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe
import qualified Data.DList as DList
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap(IntMap)
import Data.List

-- The set of positions at which a term can have critical overlaps.
newtype Positions f = Positions [Int]
type PositionsOf a = Positions (ConstantOf a)

positions :: Term f -> Positions f
positions t = Positions (aux 0 Set.empty (singleton t))
  where
    -- Consider only general superpositions.
    aux !_ !_ Empty = []
    aux n m (Cons (Var _) t) = aux (n+1) m t
    aux n m (ConsSym t@App{} u)
      | t `Set.member` m = aux (n+1) m u
      | otherwise = n:aux (n+1) (Set.insert t m) u

-- A critical overlap of one rule with another.
data Overlap f =
  Overlap {
    overlap_top   :: Term f,
    overlap_left  :: Term f,
    overlap_right :: Term f,
    overlap_inner :: Term f,
    overlap_sub   :: TriangleSubst f }
type OverlapOf a = Overlap (ConstantOf a)

-- Compute all overlaps of a rule with a set of rules.
-- N.B. This function is marked INLINE so that it fuses.
{-# INLINE overlaps #-}
overlaps :: (a -> Rule f) -> (a -> Positions f) -> [a] -> Positions f -> Rule f -> [(a, Overlap f)]
overlaps rule positions rules p1 r1 =
  [ (r2, o) | r2 <- rules, o <- symmetricOverlaps p1 r1' (positions r2) (rule r2) ]
  where
    !r1' = renameAvoiding (map rule rules) r1

-- Compute all overlaps of two rules. They should have no
-- variables in common.
{-# INLINE symmetricOverlaps #-}
symmetricOverlaps :: Positions f -> Rule f -> Positions f -> Rule f -> [Overlap f]
symmetricOverlaps p1 r1 p2 r2 =
  asymmetricOverlaps p1 r1 r2 ++ asymmetricOverlaps p2 r2 r1

{-# INLINE asymmetricOverlaps #-}
asymmetricOverlaps :: Positions f -> Rule f -> Rule f -> [Overlap f]
asymmetricOverlaps (Positions ns) (Rule _ !outer !outer') (Rule _ !inner !inner') = do
  n <- ns
  let t = at n (singleton outer)
  sub <- maybeToList (unifyTri inner t)
  return Overlap {
    overlap_top   = subst sub outer,
    overlap_left  = subst sub outer',
    overlap_right =
      build (replacePositionSub (evalSubst sub) n (singleton inner') (singleton outer)),
    overlap_inner = subst sub inner,
    overlap_sub   = sub }

-- Is a superposition prime?
isPrime :: Function f => Index (Rule f) -> Overlap f -> Bool
isPrime idx overlap =
  not (canSimplifyList idx (children (overlap_inner overlap)))
