-- Critical pairs.
{-# LANGUAGE BangPatterns, FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses, RecordWildCards, OverloadedStrings, TypeFamilies #-}
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
    overlap_top   :: {-# UNPACK #-} !(Term f),
    overlap_inner :: {-# UNPACK #-} !(Term f),
    overlap_pos   :: {-# UNPACK #-} !Int,
    overlap_eqn   :: {-# UNPACK #-} !(Equation f),
    overlap_sub   :: !(TriangleSubst f) }
  deriving Show
type OverlapOf a = Overlap (ConstantOf a)

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
    overlapAt idx n r1 r2 >>=
    simplifyOverlap idx

-- Create an overlap at a particular position in a term.
-- Doesn't simplify or check for primeness.
{-# INLINE overlapAt #-}
overlapAt ::
  (Function f, Has a (Rule f)) =>
  Index f a -> Int -> Rule f -> Rule f -> Maybe (Overlap f)
overlapAt !idx !n (Rule _ !outer !outer') (Rule _ !inner !inner') = do
  let t = at n (singleton outer)
  sub <- unifyTri inner t
  let
    top = {-# SCC overlap_top #-} termSubst sub outer
    innerTerm = {-# SCC overlap_inner #-} termSubst sub inner
    -- Make sure to keep in sync with overlapProof
    lhs = {-# SCC overlap_eqn_1 #-} termSubst sub outer'
    rhs = {-# SCC overlap_eqn_2 #-}
      buildReplacePositionSub sub n (singleton inner') (singleton outer)

  guard (lhs /= rhs)
  return Overlap {
    overlap_top = top,
    overlap_inner = innerTerm,
    overlap_pos = n,
    overlap_eqn = lhs :=: rhs,
    overlap_sub = sub }

-- Simplify an overlap and remove it if it's not prime.
{-# INLINE simplifyOverlap #-}
simplifyOverlap :: (Function f, Has a (Rule f)) => Index f a -> Overlap f -> Maybe (Overlap f)
simplifyOverlap idx overlap@Overlap{overlap_eqn = lhs :=: rhs, ..}
  | lhs' == rhs' = Nothing
  | App _ ts <- overlap_inner, canSimplifyList idx ts = Nothing
  | otherwise = Just overlap{overlap_eqn = lhs' :=: rhs'}
  where
    lhs' = simplify idx lhs
    rhs' = simplify idx rhs

-- Put these in separate functions to avoid code blowup
buildReplacePositionSub :: TriangleSubst f -> Int -> TermList f -> TermList f -> Term f
buildReplacePositionSub !sub !n !inner' !outer =
  build (replacePositionSub sub n inner' outer)

termSubst :: TriangleSubst f -> Term f -> Term f
termSubst sub t = build (Term.subst sub t)

-- Return a proof for a critical pair.
overlapProof ::
  forall a f.
  (Has a (Rule f), Has a VersionedId) =>
  a -> a -> Overlap f -> Proof f
overlapProof left right Overlap{..} =
  [Backwards (Step (the left) (the left) sub),
   Forwards $
     Parallel
       [(pos, Step (the right) (the right) sub)]
       overlap_top]
  where
    sub = close overlap_sub
    -- overlap_pos is given in terms of lhs (the left),
    -- but pos must be a position in overlap_top, which
    -- is lhs (the left) with the subsitution applied.
    pos =
      pathToPosition overlap_top $
      positionToPath (lhs (the left) :: Term f) $
      overlap_pos

-- The critical pair ordering heuristic.
data Config =
  Config {
    cfg_lhsweight :: !Int,
    cfg_rhsweight :: !Int,
    cfg_funweight :: !Int,
    cfg_varweight :: !Int }

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
      (length (filter isVar (subterms t)) + length (nub (vars t))) *
      (cfg_funweight - cfg_varweight)
