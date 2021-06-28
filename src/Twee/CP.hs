-- | Critical pair generation.
{-# LANGUAGE BangPatterns, FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses, RecordWildCards, OverloadedStrings, TypeFamilies, GeneralizedNewtypeDeriving #-}
module Twee.CP where

import qualified Twee.Term as Term
import Twee.Base
import Twee.Rule
import Twee.Index(Index)
import qualified Data.Set as Set
import Control.Monad
import Data.List hiding (singleton)
import qualified Data.ChurchList as ChurchList
import Data.ChurchList (ChurchList(..))
import Twee.Utils
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof(Derivation, congPath)
import Data.Bits

-- | The set of positions at which a term can have critical overlaps.
data Positions f = NilP | ConsP {-# UNPACK #-} !Int !(Positions f)
type PositionsOf a = Positions (ConstantOf a)
-- | Like Positions but for an equation (one set of positions per term).
data Positions2 f = ForwardsPos !(Positions f) | BothPos !(Positions f) !(Positions f)

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

-- | Calculate the set of positions for a rule.
positionsRule :: Rule f -> Positions2 f
positionsRule rule
  | oriented (orientation rule) ||
    canonicalise rule == canonicalise (backwards rule) =
    ForwardsPos (positions (lhs rule))
  | otherwise = BothPos (positions (lhs rule)) (positions (rhs rule))

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
data Overlap a f =
  Overlap {
    -- | The rule which applies at the root.
    overlap_rule1 :: !a,
    -- | The rule which applies at some subterm.
    overlap_rule2 :: !a,
    -- | The position in the critical term which is rewritten.
    overlap_how   :: {-# UNPACK #-} !How,
    -- | The top term of the critical pair
    overlap_top   :: {-# UNPACK #-} !(Term f),
    -- | The critical pair itself.
    overlap_eqn   :: {-# UNPACK #-} !(Equation f) }
  deriving Show

data Direction = Forwards | Backwards deriving (Eq, Enum, Show)

direct :: Rule f -> Direction -> Rule f
direct rule Forwards = rule
direct rule Backwards = backwards rule

data How =
  How {
    how_dir1 :: !Direction,
    how_dir2 :: !Direction,
    how_pos  :: {-# UNPACK #-} !Int }
  deriving Show

packHow :: How -> Int
packHow How{..} =
  fromEnum how_dir1 +
  fromEnum how_dir2 `shiftL` 1 +
  how_pos `shiftL` 2

unpackHow :: Int -> How
unpackHow n =
  How {
    how_dir1 = toEnum (n .&. 1),
    how_dir2 = toEnum ((n `shiftR` 1) .&. 1),
    how_pos  = n `shiftR` 2 }

-- | Represents the depth of a critical pair.
newtype Depth = Depth Int deriving (Eq, Ord, Num, Real, Enum, Integral, Show)

-- | Compute all overlaps of a rule with a set of rules.
{-# INLINEABLE overlaps #-}
overlaps ::
  forall a b f. (Function f, Has a (Rule f), Has b (Rule f), Has b (Positions2 f)) =>
  Index f a -> [b] -> b -> [Overlap b f]
overlaps idx rules r =
  ChurchList.toList (overlapsChurch idx rules r)

{-# INLINE overlapsChurch #-}
overlapsChurch :: forall f a b.
  (Function f, Has a (Rule f), Has b (Rule f), Has b (Positions2 f)) =>
  Index f a -> [b] -> b -> ChurchList (Overlap b f)
overlapsChurch idx rules r1 = do
  (d1, pos1, eq1) <- directions r1' (the r1)
  r2 <- ChurchList.fromList rules
  (d2, pos2, eq2) <- directions (the r2) (the r2)
  asymmetricOverlaps idx r1 r2 d1 d2 pos1 eq1 eq2 `mplus`
    asymmetricOverlaps idx r2 r1 d2 d1 pos2 eq2 eq1
  where
    !r1' = renameAvoiding (map the rules :: [Rule f]) (the r1)

{-# INLINE directions #-}
directions :: Rule f -> Positions2 f -> ChurchList (Direction, Positions f, Equation f)
directions rule (ForwardsPos posf) =
  return (Forwards, posf, lhs rule :=: rhs rule)
directions rule (BothPos posf posb) =
  return (Forwards, posf, lhs rule :=: rhs rule) `mplus`
  return (Backwards, posb, rhs rule :=: lhs rule)

{-# INLINE asymmetricOverlaps #-}
asymmetricOverlaps ::
  (Function f, Has a (Rule f)) =>
  Index f a -> b -> b -> Direction -> Direction -> Positions f -> Equation f -> Equation f -> ChurchList (Overlap b f)
asymmetricOverlaps idx r1 r2 d1 d2 posns eq1 eq2 = do
  n <- positionsChurch posns
  ChurchList.fromMaybe $
    overlapAt' (How d1 d2 n) r1 r2 eq1 eq2 >>=
    simplifyOverlap idx

-- | Create an overlap at a particular position in a term.
-- Doesn't simplify the overlap.
{-# INLINE overlapAt #-}
{-# SCC overlapAt #-}
overlapAt :: How -> a -> a -> Rule f -> Rule f -> Maybe (Overlap a f)
overlapAt how@(How d1 d2 _) x1 x2 r1 r2 =
  overlapAt' how x1 x2 (unorient (direct r1 d1)) (unorient (direct r2 d2))

{-# INLINE overlapAt' #-}
{-# SCC overlapAt' #-}
overlapAt' :: How -> a -> a -> Equation f -> Equation f -> Maybe (Overlap a f)
overlapAt' how@How{how_pos = n} r1 r2 (!outer :=: (!outer')) (!inner :=: (!inner')) = do
  let t = at n (singleton outer)
  sub <- unifyTri inner t
  let
    -- Make sure to keep in sync with overlapProof
    top = termSubst sub outer
    lhs = termSubst sub outer'
    rhs = buildReplacePositionSub sub n (singleton inner') (singleton outer)

  guard (lhs /= rhs)
  return Overlap {
    overlap_rule1 = r1,
    overlap_rule2 = r2,
    overlap_how = how,
    overlap_top = top,
    overlap_eqn = lhs :=: rhs }

-- | Simplify an overlap and remove it if it's trivial.
{-# INLINE simplifyOverlap #-}
simplifyOverlap :: (Function f, Has a (Rule f)) => Index f a -> Overlap b f -> Maybe (Overlap b f)
simplifyOverlap idx overlap@Overlap{overlap_eqn = lhs :=: rhs, ..}
  | lhs == rhs   = Nothing
  | lhs' == rhs' = Nothing
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

-- | The configuration for the critical pair weighting heuristic.
data Config =
  Config {
    cfg_lhsweight :: !Int,
    cfg_rhsweight :: !Int,
    cfg_funweight :: !Int,
    cfg_varweight :: !Int,
    cfg_depthweight :: !Int,
    cfg_dupcost :: !Int,
    cfg_dupfactor :: !Int }

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
    cfg_dupfactor = 0 }

-- | Compute a score for a critical pair.

-- We compute:
--   cfg_lhsweight * size l + cfg_rhsweight * size r
-- where l is the biggest term and r is the smallest,
-- and variables have weight 1 and functions have weight cfg_funweight.
{-# INLINEABLE score #-}
score :: Function f => Config -> Depth -> Overlap a f -> Int
score Config{..} depth Overlap{..} =
  fromIntegral depth * cfg_depthweight +
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

----------------------------------------------------------------------
-- * Higher-level handling of critical pairs.
----------------------------------------------------------------------

-- | A critical pair together with information about how it was derived
data CriticalPair f =
  CriticalPair {
    -- | The critical pair itself.
    cp_eqn   :: {-# UNPACK #-} !(Equation f),
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
      cp_top = subst_ sub cp_top,
      cp_proof = subst_ sub cp_proof }

instance (Labelled f, PrettyTerm f) => Pretty (CriticalPair f) where
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
        cp_top   = eraseExcept (vars l) cp_top,
        cp_proof = eraseExcept (vars l) cp_proof }
    | ord == Just GT ] ++
    [ CriticalPair {
        cp_eqn   = r :=: l',
        cp_top   = eraseExcept (vars r) cp_top,
        cp_proof = Proof.symm (eraseExcept (vars r) cp_proof) }
    | ord == Just LT ] ++
    [ CriticalPair {
        cp_eqn   = l' :=: r',
        cp_top   = eraseExcept (vars l) $ eraseExcept (vars r) cp_top,
        cp_proof = eraseExcept (vars l) $ eraseExcept (vars r) cp_proof }
    | ord == Nothing ] ++

    -- Weak rules l -> l' or r -> r'
    [ CriticalPair {
        cp_eqn   = l :=: l',
        cp_top   = Nothing,
        cp_proof = cp_proof `Proof.trans` Proof.symm (erase ls cp_proof) }
    | not (null ls), ord /= Just GT ] ++
    [ CriticalPair {
        cp_eqn   = r :=: r',
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
makeCriticalPair :: (Function f, Has a (Rule f)) => Overlap a f -> CriticalPair f
makeCriticalPair Overlap{..} =
  CriticalPair overlap_eqn
    (Just overlap_top)
    proof
  where
    left = direct (the overlap_rule1) (how_dir1 overlap_how)
    right = direct (the overlap_rule2) (how_dir2 overlap_how)

    Just leftSub = match (lhs left) overlap_top
    Just rightSub = match (lhs right) inner

    path = positionToPath (lhs left) (how_pos overlap_how)
    inner = at (pathToPosition overlap_top path) (singleton overlap_top)

    proof =
      Proof.symm (ruleDerivation (subst leftSub left))
      `Proof.trans`
      congPath path overlap_top (ruleDerivation (subst rightSub right))
