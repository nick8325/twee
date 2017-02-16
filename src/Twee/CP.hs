-- Critical pairs.
{-# LANGUAGE BangPatterns, FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses, RecordWildCards, OverloadedStrings, DeriveGeneric, TypeFamilies #-}
module Twee.CP where

import qualified Twee.Term as Term
import Twee.Base
import Twee.Rule
import Twee.Index(Index)
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe
import Data.List
import qualified Twee.ChurchList as ChurchList
import Twee.ChurchList (ChurchList(..))
import Twee.Utils
import GHC.Generics

-- The set of positions at which a term can have critical overlaps.
data Positions f = NilP | ConsP {-# UNPACK #-} !Int !(Positions f)
type PositionsOf a = Positions (ConstantOf a)

instance Show (Positions f) where
  show = show . ChurchList.toList . positionsChurch

positions :: Term f -> Positions f
positions t = aux 0 Set.empty (singleton t)
  where
    -- Consider only general superpositions.
    aux !_ !_ Empty = NilP
    aux n m (Cons (Var _) t) = aux (n+1) m t
    aux n m (ConsSym t@App{} u)
      | t `Set.member` m = aux (n+1) m u
      | otherwise = ConsP n (aux (n+1) (Set.insert t m) u)

{-# INLINE positionsChurch #-}
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
    -- overlap_top and overlap_inner can be Empty to indicate
    -- that they are not present
    overlap_top   :: {-# UNPACK #-} !(TermList f),
    overlap_inner :: {-# UNPACK #-} !(TermList f),
    overlap_pos   :: {-# UNPACK #-} !Int,
    overlap_eqn   :: {-# UNPACK #-} !(Equation f) }
  deriving (Eq, Ord, Show, Generic)
type OverlapOf a = Overlap (ConstantOf a)

instance Symbolic (Overlap f) where
  type ConstantOf (Overlap f) = f
  termsDL Overlap{..} =
    termsDL overlap_top `mplus`
    termsDL overlap_inner `mplus`
    termsDL overlap_eqn
  subst_ sub Overlap{..} =
    Overlap {
      overlap_top = subst_ sub overlap_top,
      overlap_inner = subst_ sub overlap_inner,
      overlap_pos = overlap_pos,
      overlap_eqn = subst_ sub overlap_eqn }

-- Compute all overlaps of a rule with a set of rules.
{-# INLINEABLE overlaps #-}
overlaps ::
  (Function f, Has a (Rule f), Has a (Positions f)) =>
  Index f a -> [a] -> a -> [(a, a, Overlap f)]
overlaps idx rules r =
  ChurchList.toList (overlapsChurch idx rules r)

{-# INLINE overlapsChurch #-}
overlapsChurch :: forall f a.
  (Function f, Has a (Rule f), Has a (Positions f)) =>
  Index f a -> [a] -> a -> ChurchList (a, a, Overlap f)
overlapsChurch idx rules r1 = do
  r2 <- ChurchList.fromList rules
  do { o <- asymmetricOverlaps idx (the r1) r1' (the r2); return (r1, r2, o) } `mplus`
    do { o <- asymmetricOverlaps idx (the r2) (the r2) r1'; return (r2, r1, o) }
  where
    !r1' = renameAvoiding (map the rules :: [Rule f]) (the r1)

{-# INLINE asymmetricOverlaps #-}
asymmetricOverlaps ::
  (Function f, Has a (Rule f)) =>
  Index f a -> Positions f -> Rule f -> Rule f -> ChurchList (Overlap f)
asymmetricOverlaps idx posns r1 r2 = do
  n <- positionsChurch posns
  ChurchList.fromMaybe $
    overlapAt idx n r1 r2

-- Create an overlap at a particular position in a term.
{-# INLINE overlapAt #-}
overlapAt ::
  (Function f, Has a (Rule f)) =>
  Index f a -> Int -> Rule f -> Rule f -> Maybe (Overlap f)
overlapAt !idx !n (Rule _ !outer !outer') (Rule _ !inner !inner') = do
  let t = at n (singleton outer)
  sub <- unifyTri inner t
  makeOverlap idx
   ({-# SCC overlap_top #-} Term.singleton (termSubst sub outer))
   ({-# SCC overlap_inner #-} Term.singleton (termSubst sub inner))
   n
   (({-# SCC overlap_eqn_1 #-} termSubst sub outer') :=:
    {-# SCC overlap_eqn_2 #-}
    buildReplacePositionSub sub n (singleton inner') (singleton outer))

-- Create an overlap, after simplifying and checking for primeness.
{-# INLINE makeOverlap #-}
makeOverlap :: (Function f, Has a (Rule f)) => Index f a -> TermList f -> TermList f -> Int -> Equation f -> Maybe (Overlap f)
makeOverlap idx top inner n eqn
  | trivial eqn = Nothing
  | trivial eqn' = Nothing
    -- You might think that checking for primeness first is better, to
    -- avoid having to build the equation at all if it's non-prime.
    -- But it seems to go slower!
  | ConsSym _ ts <- inner, canSimplifyList idx ts = Nothing
  | otherwise = Just (Overlap top inner n eqn')
  where
    eqn' = bothSides (simplify idx) eqn

-- Put these in separate functions to avoid code blowup
buildReplacePositionSub :: TriangleSubst f -> Int -> TermList f -> TermList f -> Term f
buildReplacePositionSub !sub !n !inner' !outer =
  build (replacePositionSub sub n inner' outer)

termSubst :: TriangleSubst f -> Term f -> Term f
termSubst sub t = build (Term.subst sub t)

-- Simplify an existing overlap.
{-# INLINEABLE simplifyOverlap #-}
simplifyOverlap :: (Function f, Has a (Rule f)) => Index f a -> Overlap f -> Maybe (Overlap f)
simplifyOverlap idx Overlap{..} =
  makeOverlap idx overlap_top overlap_inner overlap_pos overlap_eqn

-- The critical pair ordering heuristic.
data Config =
  Config {
    cfg_lhsweight :: !Int,
    cfg_rhsweight :: !Int,
    cfg_funweight :: !Int,
    cfg_varweight :: !Int,
    cfg_repeats   :: !Bool }

-- We compute:
--   cfg_lhsweight * size l + cfg_rhsweight * size r
-- where l is the biggest term and r is the smallest,
-- and variables have weight 1 and functions have weight cfg_funweight.
score :: Function f => Config -> Overlap f -> Int
score config overlap@Overlap{overlap_eqn = t :=: u}
  | isInequality t u || isInequality u t =
    score config overlap{overlap_eqn = true :=: false } + 1
    where
      isInequality (App eq (Cons t (Cons u Empty))) (App false Empty) =
        eq == equalsCon && false == falseCon && isJust (unify t u)
      isInequality _ _ = False

      true  = build (con trueCon)
      false = build (con falseCon)
score Config{..} Overlap{..} =
  (m + n) * cfg_rhsweight +
  intMax m n * (cfg_lhsweight - cfg_rhsweight)
  where
    l :=: r = overlap_eqn
    m = size l
    n = size r

    size t =
      len t * cfg_funweight -
      (length (filter isVar (subterms t)) +
       if cfg_repeats then length (nub (vars t)) else 0) *
      (cfg_funweight - cfg_varweight)
