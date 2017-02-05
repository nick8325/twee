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
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap(IntMap)
import Data.List

-- The set of positions at which a term can have critical overlaps.
newtype Positions f = Positions [Int]
type PositionsOf a = Positions (ConstantOf a)

positions :: Term f -> Positions f
positions t = Positions (aux 0 Set.empty (singleton t))
  where
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

-- Compute all overlaps of two rules. They should have no
-- variables in common.
{-# INLINE overlaps1 #-}
overlaps1 :: Positions f -> Rule f -> Rule f -> [Overlap f]
overlaps1 (Positions ns) (Rule _ !outer !outer') (Rule _ !inner !inner') = do
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

-- Compute all overlaps of a rule with a set of rules.
{-# INLINE overlaps #-}
overlaps :: (a -> Rule f) -> (a -> Positions f) -> [a] -> Positions f -> Rule f -> [(a, Overlap f)]
overlaps rule positions rules p1 r1 =
  [ (r2, o) | r2 <- rules, o <- overlaps1 (positions r2) (rule r2) r1' ] ++
  [ (r2, o) | r2 <- rules, o <- overlaps1 p1 r1' (rule r2) ]
  where
    !r1' = renameAvoiding (map rule rules) r1

data RulePos f =
  RulePos {
    rp_id   :: {-# UNPACK #-} !Int,
    rp_rule :: {-# UNPACK #-} !(Rule f),
    rp_pos  :: !(Positions f) }

blah :: [RulePos f] -> RulePos f -> Int
blah rules !r = foldl' min 0 (map (rp_id . fst) (filter (uncurry p) (overlaps rp_rule rp_pos rules (rp_pos r) (rp_rule r))))
  where
    p rp _ = rp_id rp >= 3
