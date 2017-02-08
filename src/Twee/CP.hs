-- Critical pairs.
{-# LANGUAGE BangPatterns, FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses, RecordWildCards #-}
module Twee.CP where

import qualified Twee.Term as Term
import Twee.Base
import Twee.Rule
import Twee.Index(Index)
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe
import qualified Data.DList as DList
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap(IntMap)
import Data.List
import qualified Twee.ChurchList as ChurchList
import Twee.ChurchList (ChurchList(..))
import Control.Arrow((***))
import GHC.Magic(oneShot, inline)
import Data.Monoid
import Twee.Utils

-- The set of positions at which a term can have critical overlaps.
data Positions f = NilP | ConsP {-# UNPACK #-} !Int !(Positions f)
type PositionsOf a = Positions (ConstantOf a)

positions :: Term f -> Positions f
positions t = aux 0 Set.empty (singleton t)
  where
    -- Consider only general superpositions.
    aux !_ !_ Empty = NilP
    aux n m (Cons (Var _) t) = aux (n+1) m t
    aux n m (ConsSym t@App{} u)
      | t `Set.member` m = aux (n+1) m u
      | otherwise = ConsP n (aux (n+1) (Set.insert t m) u)

positionsChurch :: Positions f -> ChurchList Int
positionsChurch posns =
  ChurchList $ \c n ->
    let
      pos NilP = n
      pos (ConsP x posns) = c x (pos posns)
    in
      pos posns

-- A critical overlap of one rule with another.
data Overlap f =
  Overlap {
    overlap_top   :: Maybe (Term f),
    overlap_inner :: {-# UNPACK #-} !(Term f),
    overlap_eqn   :: {-# UNPACK #-} !(Equation f) }
type OverlapOf a = Overlap (ConstantOf a)

-- Compute all overlaps of a rule with a set of rules.
overlaps :: forall f a.
  (Function f, Has a (Rule f), Has a (Positions f)) =>
  Index f a -> [a] -> a -> [(a, Overlap f)]
overlaps idx rules r =
  ChurchList.toList (overlapsChurch idx rules r)

{-# INLINE overlapsChurch #-}
overlapsChurch :: forall f a.
  (Function f, Has a (Rule f), Has a (Positions f)) =>
  Index f a -> [a] -> a -> ChurchList (a, Overlap f)
overlapsChurch idx rules r1 = do
  r2 <- ChurchList.fromList rules
  o <- symmetricOverlaps idx (the r1) r1' (the r2) (the r2)
  return (r2, o)
  where
    !r1' = renameAvoiding (map the rules :: [Rule f]) (the r1)

-- Compute all overlaps of two rules. They should have no
-- variables in common.
{-# INLINE symmetricOverlaps #-}
symmetricOverlaps ::
  (Function f, Has a (Rule f)) =>
  Index f a -> Positions f -> Rule f -> Positions f -> Rule f -> ChurchList (Overlap f)
symmetricOverlaps idx p1 r1 p2 r2 =
  asymmetricOverlaps idx p1 r1 r2 `mplus` asymmetricOverlaps idx p2 r2 r1

{-# INLINE asymmetricOverlaps #-}
asymmetricOverlaps ::
  (Function f, Has a (Rule f)) =>
  Index f a -> Positions f -> Rule f -> Rule f -> ChurchList (Overlap f)
asymmetricOverlaps idx posns (Rule _ !outer !outer') (Rule _ !inner !inner') = do
  n <- positionsChurch posns
  let t = at n (singleton outer)
  sub <- ChurchList.fromMaybe (unifyTri inner t)
  ChurchList.fromMaybe $
    makeOverlap idx
     (Just $! termSubst sub outer)
     (termSubst sub inner)
     (termSubst sub outer' :=:
      buildReplacePositionSub sub n (singleton inner') (singleton outer))

-- Put these in separate functions to avoid code blowup
buildReplacePositionSub :: TriangleSubst f -> Int -> TermList f -> TermList f -> Term f
buildReplacePositionSub !sub !n !inner' !outer =
  build (replacePositionSub (evalSubst sub) n inner' outer)
termSubst :: TriangleSubst f -> Term f -> Term f
termSubst sub t = build (Term.subst sub t)

-- Create an overlap, after simplifying and checking for primeness.
{-# INLINE makeOverlap #-}
makeOverlap :: (Function f, Has a (Rule f)) => Index f a -> Maybe (Term f) -> Term f -> Equation f -> Maybe (Overlap f)
makeOverlap idx top inner eqn
    -- Check for primeness before forcing anything else
  | canSimplifyList idx (children inner) = Nothing
  | trivial eqn' = Nothing
  | otherwise = Just (Overlap top inner eqn')
  where
    eqn' = bothSides (simplify idx) eqn

-- Simplify an existing overlap.
simplifyOverlap :: (Function f, Has a (Rule f)) => Index f a -> Overlap f -> Maybe (Overlap f)
simplifyOverlap idx Overlap{..} =
  makeOverlap idx overlap_top overlap_inner overlap_eqn

-- The critical pair ordering heuristic.
data Config =
  Config {
    config_lhsweight :: !Int,
    config_funweight :: !Int }

-- We compute:
--   config_lhsweight * size l + size r
-- where l is the biggest term and r is the smallest,
-- and variables have weight 1 and functions have weight config_funweight.
score :: Config -> Overlap f -> Int
score Config{..} Overlap{..} =
  m + n + intMax m n * (config_lhsweight - 1)
  where
    l :=: r = overlap_eqn
    m = size l
    n = size r

    size t =
      len t * config_funweight -
      length (filter isVar (subterms t)) * (config_funweight - 1)

data Best = Best {-# UNPACK #-} !Id {-# UNPACK #-} !Int

{-# INLINEABLE bestOverlap #-}
bestOverlap :: forall f a.
  (Function f, Has a (Rule f), Has a (Positions f), Has a Id) =>
  Config -> Index f a -> [a] -> a -> Maybe Best
bestOverlap config idx rules r =
  best config (overlapsChurch idx rules r)

{-# INLINE best #-}
best :: Has a Id => Config -> ChurchList (a, Overlap f) -> Maybe Best
best !config overlaps
  | n == maxBound = Nothing
  | otherwise = Just x
  where
    -- Use maxBound to indicate no critical pair.
    -- Do this instead of using Maybe to get better unboxing.
    x@(Best _ n) =
      ChurchList.foldl' op (Best (Id 0) maxBound) $
      fmap (\(x, o) -> Best (the x) (score config o)) $
      overlaps

    op x@(Best _ m) y@(Best _ n)
      | m <= n = x
      | otherwise = y
