-- | Critical pair generation.
{-# LANGUAGE BangPatterns, FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses, RecordWildCards, OverloadedStrings, TypeFamilies, GeneralizedNewtypeDeriving #-}
module Twee.CP where

import qualified Twee.Term as Term
import Twee.Base
import Twee.Rule
import Twee.Index(Index)
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad
import Data.List
import qualified Data.ChurchList as ChurchList
import Data.ChurchList (ChurchList(..))
import Twee.Utils
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof(Derivation, Proof, congPath)

-- | The set of positions at which a term can have critical overlaps.
data Positions f = NilP | ConsP {-# UNPACK #-} !Int !(Positions f)
type PositionsOf a = Positions (ConstantOf a)

instance Show (Positions f) where
  show = show . ChurchList.toList . positionsChurch

-- | Calculate the set of positions for a term.
positions :: Term f -> Positions f
positions t = aux 0 Set.empty (singleton t)
  where
    -- Consider only general superpositions.
    aux !_ !_ Empty = NilP
    aux n m (Cons (Var _) t) = aux (n+1) m t
    aux n m ConsSym{hd = t@App{}, rest = u}
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

-- | A critical overlap of one rule with another.
data Overlap f =
  Overlap {
    -- | The depth (1 for CPs of axioms, 2 for CPs whose rules have depth 1, etc.)
    overlap_depth :: {-# UNPACK #-} !Depth,
    -- | The critical term.
    overlap_top   :: {-# UNPACK #-} !(Term f),
    -- | The part of the critical term which the inner rule rewrites.
    overlap_inner :: {-# UNPACK #-} !(Term f),
    -- | The position in the critical term which is rewritten.
    overlap_pos   :: {-# UNPACK #-} !Int,
    -- | The critical pair itself.
    overlap_eqn   :: {-# UNPACK #-} !(Equation f) }
  deriving Show
type OverlapOf a = Overlap (ConstantOf a)

-- | Represents the depth of a critical pair.
newtype Depth = Depth Int deriving (Eq, Ord, Num, Real, Enum, Integral, Show)

-- | Compute all overlaps of a rule with a set of rules.
{-# INLINEABLE overlaps #-}
overlaps ::
  forall a f. (Function f, Has a Id, Has a (Rule f), Has a (Positions f), Has a Depth) =>
  Depth -> Index f a -> [a] -> a -> [(a, a, Overlap f)]
overlaps max_depth idx rules r =
  ChurchList.toList (overlapsChurch max_depth idx rules r)

{-# INLINE overlapsChurch #-}
overlapsChurch :: forall f a.
  (Function f, Has a (Rule f), Has a (Positions f), Has a Depth) =>
  Depth -> Index f a -> [a] -> a -> ChurchList (a, a, Overlap f)
overlapsChurch max_depth idx rules r1 = do
  guard (the r1 < max_depth)
  r2 <- ChurchList.fromList rules
  guard (the r2 < max_depth)
  let !depth = 1 + max (the r1) (the r2)
  do { o <- asymmetricOverlaps idx depth (the r1) r1' (the r2); return (r1, r2, o) } `mplus`
    do { o <- asymmetricOverlaps idx depth (the r2) (the r2) r1'; return (r2, r1, o) }
  where
    !r1' = renameAvoiding (map the rules :: [Rule f]) (the r1)

{-# INLINE asymmetricOverlaps #-}
asymmetricOverlaps ::
  (Function f, Has a (Rule f), Has a Depth) =>
  Index f a -> Depth -> Positions f -> Rule f -> Rule f -> ChurchList (Overlap f)
asymmetricOverlaps idx depth posns r1 r2 = do
  n <- positionsChurch posns
  ChurchList.fromMaybe $
    overlapAt n depth r1 r2 >>=
    simplifyOverlap idx

-- | Create an overlap at a particular position in a term.
-- Doesn't simplify the overlap.
{-# INLINE overlapAt #-}
{-# SCC overlapAt #-}
overlapAt :: Int -> Depth -> Rule f -> Rule f -> Maybe (Overlap f)
overlapAt !n !depth (Rule _ _ !outer !outer') (Rule _ _ !inner !inner') = do
  let t = at n (singleton outer)
  sub <- unifyTri inner t
  let
    top = termSubst sub outer
    innerTerm = termSubst sub inner
    -- Make sure to keep in sync with overlapProof
    lhs = termSubst sub outer'
    rhs = buildReplacePositionSub sub n (singleton inner') (singleton outer)

  guard (lhs /= rhs)
  return Overlap {
    overlap_depth = depth,
    overlap_top = top,
    overlap_inner = innerTerm,
    overlap_pos = n,
    overlap_eqn = lhs :=: rhs }

-- | Simplify an overlap and remove it if it's trivial.
{-# INLINE simplifyOverlap #-}
simplifyOverlap :: (Function f, Has a (Rule f)) => Index f a -> Overlap f -> Maybe (Overlap f)
simplifyOverlap idx overlap@Overlap{overlap_eqn = lhs :=: rhs, ..}
  | lhs == rhs   = Nothing
  | lhs' == rhs' = Nothing
  | otherwise = Just overlap{overlap_eqn = lhs' :=: rhs'}
  where
    lhs' = simplify idx lhs
    rhs' = simplify idx rhs

-- Put these in separate functions to avoid code blowup
buildReplacePositionSub :: (Substitution s, SubstFun s ~ f) => s -> Int -> TermList f -> TermList f -> Term f
buildReplacePositionSub !sub !n !inner' !outer =
  build (replacePositionSub sub n inner' outer)

termSubst :: TriangleSubst f -> Term f -> Term f
termSubst sub t = build (Term.subst sub t)

-- | The configuration for the critical pair weighting heuristic.
data Config =
  Config {
    cfg_lhsweight :: !Int,
    cfg_rhsweight :: !Int,
    cfg_funweight :: !Int,
    cfg_varweight :: !Int,
    cfg_depthweight :: !Int,
    cfg_dupcost :: !Int,
    cfg_dupfactor :: !Int,
    cfg_goal_bonus :: !Bool }

-- | The default heuristic configuration.
defaultConfig :: Config
defaultConfig =
  Config {
    cfg_lhsweight = 4,
    cfg_rhsweight = 1,
    cfg_funweight = 7,
    cfg_varweight = 6,
    cfg_depthweight = 16,
    cfg_dupcost = 7,
    cfg_dupfactor = 0,
    cfg_goal_bonus = False }

-- | Compute a score for a critical pair.

-- We compute:
--   cfg_lhsweight * size l + cfg_rhsweight * size r
-- where l is the biggest term and r is the smallest,
-- and variables have weight 1 and functions have weight cfg_funweight.
{-# INLINEABLE score #-}
score :: Function f => Config -> [Set (Term f)] -> Overlap f -> Int
score Config{..} goalss Overlap{..}
  | cfg_goal_bonus && (reducesGoal l r || reducesGoal r l) = 1
  | otherwise =
    fromIntegral overlap_depth * cfg_depthweight +
    (m + n) * cfg_rhsweight +
    intMax m n * (cfg_lhsweight - cfg_rhsweight)
    where
    l :=: r = overlap_eqn
    m = size' 0 (singleton l)
    n = size' 0 (singleton r)

    size' !n Empty = n
    size' n (Cons t ts)
      | len t > 1, t `isSubtermOfList` ts =
        size' (n+cfg_dupcost+cfg_dupfactor*len t) ts
    size' n ts
      | Cons (App f ws@(Cons a (Cons b us))) vs <- ts,
        not (isVar a),
        not (isVar b),
        hasEqualsBonus (fun_value f),
        Just sub <- unify a b =
        size' (n+cfg_funweight) ws `min`
        size' (size' (n+1) (subst sub us)) (subst sub vs)
    size' n (Cons (Var _) ts) =
      size' (n+cfg_varweight) ts
    size' n ConsSym{hd = App{}, rest = ts} =
      size' (n+cfg_funweight) ts

    reducesGoal t u = not $ ChurchList.null $ do
      goals <- ChurchList.fromList goalss
      goal <- ChurchList.fromList (Set.toList goals)
      n <- positionsChurch (positions goal)
      let subgoal = at n (singleton goal)
      sub <- ChurchList.fromMaybe (match t subgoal)
      let u' = buildReplacePositionSub sub n (singleton u) (singleton goal)
      guard (u' `notElem` goals && u' /= goal && lessEqSkolem u' goal)

----------------------------------------------------------------------
-- * Higher-level handling of critical pairs.
----------------------------------------------------------------------

-- | A critical pair together with information about how it was derived
data CriticalPair f =
  CriticalPair {
    -- | The critical pair itself.
    cp_eqn   :: {-# UNPACK #-} !(Equation f),
    -- | The depth of the critical pair.
    cp_depth :: {-# UNPACK #-} !Depth,
    -- | The critical term, if there is one.
    -- (Axioms do not have a critical term.)
    cp_top   :: !(Maybe (Term f)),
    -- | A derivation of the critical pair from the axioms.
    cp_proof :: !(Derivation f) }

instance Symbolic (CriticalPair f) where
  type ConstantOf (CriticalPair f) = f
  termsDL CriticalPair{..} =
    termsDL cp_eqn `mplus` termsDL cp_top `mplus` termsDL cp_proof
  subst_ sub CriticalPair{..} =
    CriticalPair {
      cp_eqn = subst_ sub cp_eqn,
      cp_depth = cp_depth,
      cp_top = subst_ sub cp_top,
      cp_proof = subst_ sub cp_proof }

instance PrettyTerm f => Pretty (CriticalPair f) where
  pPrint CriticalPair{..} =
    vcat [
      pPrint cp_eqn,
      nest 2 (text "top:" <+> pPrint cp_top) ]

-- | Split a critical pair so that it can be turned into rules.
--
-- The resulting critical pairs have the property that no variable appears on
-- the right that is not on the left.

-- See the comment below.
split :: Function f => CriticalPair f -> [CriticalPair f]
split CriticalPair{cp_eqn = l :=: r, ..}
  | l == r = []
  | otherwise =
    -- If we have something which is almost a rule, except that some
    -- variables appear only on the right-hand side, e.g.:
    --   f x y -> g x z
    -- then we replace it with the following two rules:
    --   f x y -> g x ?
    --   g x z -> g x ?
    -- where the second rule is weakly oriented and ? is the minimal
    -- constant.
    --
    -- If we have an unoriented equation with a similar problem, e.g.:
    --   f x y = g x z
    -- then we replace it with potentially three rules:
    --   f x ? = g x ?
    --   f x y -> f x ?
    --   g x z -> g x ?

    -- The main rule l -> r' or r -> l' or l' = r'
    [ CriticalPair {
        cp_eqn   = l :=: r',
        cp_depth = cp_depth,
        cp_top   = eraseExcept (vars l) cp_top,
        cp_proof = eraseExcept (vars l) cp_proof }
    | ord == Just GT ] ++
    [ CriticalPair {
        cp_eqn   = r :=: l',
        cp_depth = cp_depth,
        cp_top   = eraseExcept (vars r) cp_top,
        cp_proof = Proof.symm (eraseExcept (vars r) cp_proof) }
    | ord == Just LT ] ++
    [ CriticalPair {
        cp_eqn   = l' :=: r',
        cp_depth = cp_depth,
        cp_top   = eraseExcept (vars l) $ eraseExcept (vars r) cp_top,
        cp_proof = eraseExcept (vars l) $ eraseExcept (vars r) cp_proof }
    | ord == Nothing ] ++

    -- Weak rules l -> l' or r -> r'
    [ CriticalPair {
        cp_eqn   = l :=: l',
        cp_depth = cp_depth + 1,
        cp_top   = Nothing,
        cp_proof = cp_proof `Proof.trans` Proof.symm (erase ls cp_proof) }
    | not (null ls), ord /= Just GT ] ++
    [ CriticalPair {
        cp_eqn   = r :=: r',
        cp_depth = cp_depth + 1,
        cp_top   = Nothing,
        cp_proof = Proof.symm cp_proof `Proof.trans` erase rs cp_proof }
    | not (null rs), ord /= Just LT ]
    where
      ord = orientTerms l' r'
      l' = erase ls l
      r' = erase rs r
      ls = usort (vars l) \\ usort (vars r)
      rs = usort (vars r) \\ usort (vars l)

      eraseExcept vs t =
        erase (usort (vars t) \\ usort vs) t

-- | Make a critical pair from two rules and an overlap.
{-# INLINEABLE makeCriticalPair #-}
makeCriticalPair ::
  forall f a. (Has a (Rule f), Has a Id, Function f) =>
  a -> a -> Overlap f -> CriticalPair f
makeCriticalPair r1 r2 overlap@Overlap{..} =
  CriticalPair overlap_eqn
    overlap_depth
    (Just overlap_top)
    (overlapProof r1 r2 overlap)

-- | Return a proof for a critical pair.
{-# INLINEABLE overlapProof #-}
overlapProof ::
  forall a f.
  (Has a (Rule f), Has a Id) =>
  a -> a -> Overlap f -> Derivation f
overlapProof left right Overlap{..} =
  Proof.symm (rule_derivation (subst leftSub (the left)))
  `Proof.trans`
  congPath path overlap_top (rule_derivation (subst rightSub (the right)))
  where
    Just leftSub = match (lhs (the left)) overlap_top
    Just rightSub = match (lhs (the right)) overlap_inner

    path = positionToPath (lhs (the left) :: Term f) overlap_pos
