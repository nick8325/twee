{-# LANGUAGE TypeFamilies, FlexibleContexts, RecordWildCards, CPP, BangPatterns, OverloadedStrings, DeriveGeneric, MultiParamTypeClasses, ScopedTypeVariables, GeneralizedNewtypeDeriving #-}
module Twee.Rule where

#include "errors.h"
import Twee.Base
import Twee.Constraints
import qualified Twee.Index as Index
import Twee.Index(Index)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Maybe
import Data.Either
import Data.List
import Twee.Utils
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Twee.Term as Term
import GHC.Generics
import Data.Ord

--------------------------------------------------------------------------------
-- Rewrite rules.
--------------------------------------------------------------------------------

data Rule f =
  Rule {
    orientation :: !(Orientation f),
    lhs :: {-# UNPACK #-} !(Term f),
    rhs :: {-# UNPACK #-} !(Term f) }
  deriving (Eq, Ord, Show, Generic)
type RuleOf a = Rule (ConstantOf a)

data Orientation f =
    Oriented
  | WeaklyOriented {-# UNPACK #-} !(Fun f) [Term f]
  | Permutative [(Term f, Term f)]
  | Unoriented
  deriving Show

instance Eq (Orientation f) where _ == _ = True
instance Ord (Orientation f) where compare _ _ = EQ

oriented :: Orientation f -> Bool
oriented Oriented{} = True
oriented WeaklyOriented{} = True
oriented _ = False

weaklyOriented :: Orientation f -> Bool
weaklyOriented WeaklyOriented{} = True
weaklyOriented _ = False

instance Symbolic (Rule f) where
  type ConstantOf (Rule f) = f

instance f ~ g => Has (Rule f) (Term g) where
  the = lhs

instance Symbolic (Orientation f) where
  type ConstantOf (Orientation f) = f

  termsDL Oriented = mzero
  termsDL (WeaklyOriented _ ts) = termsDL ts
  termsDL (Permutative ts) = termsDL ts
  termsDL Unoriented = mzero

  subst_ _   Oriented = Oriented
  subst_ sub (WeaklyOriented min ts) = WeaklyOriented min (subst_ sub ts)
  subst_ sub (Permutative ts) = Permutative (subst_ sub ts)
  subst_ _   Unoriented = Unoriented

instance PrettyTerm f => Pretty (Rule f) where
  pPrint (Rule or l r) =
    pPrint l <+> text (showOrientation or) <+> pPrint r
    where
      showOrientation Oriented = "->"
      showOrientation WeaklyOriented{} = "~>"
      showOrientation Permutative{} = "<->"
      showOrientation Unoriented = "="

--------------------------------------------------------------------------------
-- Equations.
--------------------------------------------------------------------------------

data Equation f =
  {-# UNPACK #-} !(Term f) :=: {-# UNPACK #-} !(Term f)
  deriving (Eq, Ord, Show, Generic)
type EquationOf a = Equation (ConstantOf a)

instance Symbolic (Equation f) where
  type ConstantOf (Equation f) = f

instance PrettyTerm f => Pretty (Equation f) where
  pPrint (x :=: y) = pPrint x <+> text "=" <+> pPrint y

instance Sized f => Sized (Equation f) where
  size (x :=: y) = size x + size y

-- Order an equation roughly left-to-right.
-- However, there is no guarantee that the result is oriented.
order :: Function f => Equation f -> Equation f
order (l :=: r)
  | l == r = l :=: r
  | otherwise =
    case compare (size l) (size r) of
      LT -> r :=: l
      GT -> l :=: r
      EQ -> if lessEq l r then r :=: l else l :=: r

-- Turn a rule into an equation.
unorient :: Rule f -> Equation f
unorient (Rule _ l r) = l :=: r

-- Turn an equation into a set of rules.
-- Along with each rule, returns a function which transforms a proof
-- of the equation into a proof of the rule.
orient :: forall f. Function f => Equation f -> [(Rule f, Proof f -> Proof f)]
orient (l :=: r) | l == r = []
orient (l :=: r) =
  -- If we have an equation where some variables appear only on one side, e.g.:
  --   f x y = g x z
  -- then replace it with the equations:
  --   f x y = f x k
  --   g x z = g x k
  --   f x k = g x k
  -- where k is an arbitrary constant
  [ (makeRule l r',
     \pf -> erase rs pf)
  | ord /= Just LT && ord /= Just EQ ] ++
  [ (makeRule r l',
     \pf -> backwards (erase ls pf))
  | ord /= Just GT && ord /= Just EQ ] ++
  [ (makeRule l l',
     \pf -> pf `mappend` backwards (erase ls pf))
  | not (null ls), ord /= Just GT ] ++
  [ (makeRule r r',
     \pf -> backwards pf `mappend` erase rs pf)
  | not (null rs), ord /= Just LT ]
  where
    ord = orientTerms l' r'
    l' = erase ls l
    r' = erase rs r
    ls = usort (vars l) \\ usort (vars r)
    rs = usort (vars r) \\ usort (vars l)

    erase :: (Symbolic a, ConstantOf a ~ f) => [Var] -> a -> a
    erase [] t = t
    erase xs t = subst sub t
      where
        sub = fromMaybe __ $ flattenSubst [(x, minimalTerm) | x <- xs]

-- Turn a pair of terms t and u into a rule t -> u by computing the
-- orientation info (e.g. oriented, permutative or unoriented).
makeRule :: Function f => Term f -> Term f -> Rule f
makeRule t u = Rule o t u
  where
    o | lessEq u t =
        case unify t u of
          Nothing -> Oriented
          Just sub
            | allSubst (\_ (Cons t Empty) -> isMinimal t) sub ->
              WeaklyOriented minimal (map (build . var . fst) (listSubst sub))
            | otherwise -> Unoriented
      | lessEq t u = ERROR("wrongly-oriented rule")
      | not (null (usort (vars u) \\ usort (vars t))) =
        ERROR("unbound variables in rule")
      | Just ts <- evalStateT (makePermutative t u) [],
        permutativeOK t u ts =
        Permutative ts
      | otherwise = Unoriented

    permutativeOK _ _ [] = True
    permutativeOK t u ((Var x, Var y):xs) =
      lessIn model u t == Just Strict &&
      permutativeOK t' u' xs
      where
        model = modelFromOrder [Variable y, Variable x]
        sub x' = if x == x' then var y else var x'
        t' = subst sub t
        u' = subst sub u

    makePermutative t u = do
      msub <- gets flattenSubst
      sub  <- lift msub
      aux (subst sub t) (subst sub u)
        where
          aux (Var x) (Var y)
            | x == y = return []
            | otherwise = do
              modify ((x, build $ var y):)
              return [(build $ var x, build $ var y)]

          aux (App f ts) (App g us)
            | f == g =
              fmap concat (zipWithM makePermutative (unpack ts) (unpack us))

          aux _ _ = mzero

-- Apply a function to both sides of an equation.
bothSides :: (Term f -> Term f') -> Equation f -> Equation f'
bothSides f (t :=: u) = f t :=: f u

-- Is an equation of the form t = t?
trivial :: Eq f => Equation f -> Bool
trivial (t :=: u) = t == u

--------------------------------------------------------------------------------
-- Extra-fast rewriting, without proof output or unorientable rules.
--------------------------------------------------------------------------------

-- Compute the normal form of a term wrt only oriented rules.
{-# INLINEABLE simplify #-}
simplify :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Term f
simplify !idx !t = {-# SCC simplify #-} simplify1 idx t

{-# INLINEABLE simplify1 #-}
simplify1 :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Term f
simplify1 idx t
  | t == u = t
  | otherwise = simplify idx u
  where
    u = build (simp (singleton t))

    simp Empty = mempty
    simp (Cons (Var x) t) = var x `mappend` simp t
    simp (Cons t u)
      | Just (rule, sub) <- simpleRewrite idx t =
        Term.subst sub (rhs rule) `mappend` simp u
    simp (Cons (App f ts) us) =
      app f (simp ts) `mappend` simp us

-- Check if a term can be simplified.
{-# INLINEABLE canSimplify #-}
canSimplify :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Bool
canSimplify idx t = canSimplifyList idx (singleton t)

{-# INLINEABLE canSimplifyList #-}
canSimplifyList :: (Function f, Has a (Rule f)) => Index f a -> TermList f -> Bool
canSimplifyList idx t =
  {-# SCC canSimplifyList #-}
  any (isJust . simpleRewrite idx) (filter isApp (subtermsList t))

-- Find a simplification step that applies to a term.
{-# INLINEABLE simpleRewrite #-}
simpleRewrite :: (Function f, Has a (Rule f)) => Index f a -> Term f -> Maybe (Rule f, Subst f)
simpleRewrite idx t =
  -- Use instead of maybeToList to make fusion work
  foldr (\x _ -> Just x) Nothing $ do
    rule <- the <$> Index.approxMatches t idx
    guard (oriented (orientation rule))
    sub <- maybeToList (match (lhs rule) t)
    guard (reducesOriented rule sub)
    return (rule, sub)

--------------------------------------------------------------------------------
-- Rewriting, with proof output.
--------------------------------------------------------------------------------

type Strategy f = Term f -> [Reduction f]

-- A multi-step rewrite proof t ->* u
data Reduction f =
    -- Apply a single rewrite rule to the root of a term
    Step {-# UNPACK #-} !VersionedId !(Rule f) !(Subst f)
    -- Reflexivity
  | Refl {-# UNPACK #-} !(Term f)
    -- Transivitity
  | Trans !(Reduction f) !(Reduction f)
    -- Congruence
  | Cong {-# UNPACK #-} !(Fun f) ![Reduction f]
  deriving Show

-- Two reductions are equal if they rewrite to the same thing.
-- This is useful for normalForms.
instance Eq (Reduction f) where x == y = compare x y == EQ
instance Ord (Reduction f) where
  compare = comparing (\p -> result p)

instance Symbolic (Reduction f) where
  type ConstantOf (Reduction f) = f
  termsDL (Step _ rule sub) = termsDL rule `mplus` termsDL sub
  termsDL (Refl t) = termsDL t
  termsDL (Trans p q) = termsDL p `mplus` termsDL q
  termsDL (Cong _ ps) = termsDL ps

  subst_ sub (Step n rule s) = Step n rule (subst_ sub s)
  subst_ sub (Trans p q) = Trans (subst_ sub p) (subst_ sub q)
  subst_ sub (Refl t) = Refl (subst_ sub t)
  subst_ sub (Cong f ps) = Cong f (subst_ sub ps)

instance PrettyTerm f => Pretty (Reduction f) where
  pPrint = pPrint . reductionProof

-- Smart constructors for Trans and Cong which simplify Refl.
trans :: Reduction f -> Reduction f -> Reduction f
trans Refl{} p = p
trans p Refl{} = p
-- Make right-associative to improve performance of 'result'
trans p (Trans q r) = Trans (Trans p q) r
trans p q = Trans p q

cong :: Fun f -> [Reduction f] -> Reduction f
cong f ps
  | all isRefl ps = Refl (result (Cong f ps))
  | otherwise = Cong f ps
  where
    isRefl Refl{} = True
    isRefl _ = False

-- Applies a reduction at a particular path in a term.
congPath :: [Int] -> Term f -> Reduction f -> Reduction f
congPath [] _ p = p
congPath (n:ns) (App f t) p | n <= length ts =
  cong f $
    map Refl (take n ts) ++
    [congPath ns (ts !! n) p] ++
    map Refl (drop (n+1) ts)
  where
    ts = unpack t
congPath _ _ _ = error "bad path"

-- Find the initial term of a rewrite proof.
initial :: Reduction f -> Term f
initial (Trans p _) = initial p
initial (Refl t) = t
initial p = {-# SCC result_emitInitial #-} build (emitInitial p)
  where
    emitInitial (Step _ r sub) = Term.subst sub (lhs r)
    emitInitial (Refl t) = builder t
    emitInitial (Trans p q) = emitInitial p
    emitInitial (Cong f ps) = app f (map emitInitial ps)

-- Find the final term of a rewrite proof.
result :: Reduction f -> Term f
result (Trans _ q) = result q
result (Refl t) = t
result p = {-# SCC result_emitResult #-} build (emitResult p)
  where
    emitResult (Step _ r sub) = Term.subst sub (rhs r)
    emitResult (Refl t) = builder t
    emitResult (Trans _ q) = emitResult q
    emitResult (Cong f ps) = app f (map emitResult ps)

-- Check a rewrite proof for validity, given the initial and final terms.
verifyReduction :: Term f -> Term f -> Reduction f -> Bool
verifyReduction t u (Step _ r sub) =
  subst sub (lhs r) == t && subst sub (rhs r) == u
verifyReduction t u (Refl v) = t == u && u == v
verifyReduction t v (Trans p q) =
  verifyReduction t u p && verifyReduction u v q
  where
    u = result p
verifyReduction (App f1 t) (App f2 u) (Cong f3 ps) =
  f1 == f2 && f2 == f3 &&
  length ts == length us && length us == length ps &&
  and (zipWith3 verifyReduction ts us ps)
  where
    ts = unpack t
    us = unpack u
verifyReduction _ _ _ = False

-- The list of all rewrite rules used in a proof
steps :: Reduction f -> [(VersionedId, Rule f, Subst f)]
steps r = aux r []
  where
    aux (Step n r sub) = ((n, r, sub):)
    aux (Refl _) = id
    aux (Trans p q) = aux p . aux q
    aux (Cong _ ps) = foldr (.) id (map aux ps)

--------------------------------------------------------------------------------
-- Strategy combinators.
--------------------------------------------------------------------------------

-- Normalise a term wrt a particular strategy.
{-# INLINE normaliseWith #-}
normaliseWith :: PrettyTerm f => (Term f -> Bool) -> Strategy f -> Term f -> Reduction f
normaliseWith ok strat t = {-# SCC normaliseWith #-} res
  where
    res = aux 0 (Refl t) t
    aux 1000 p _ =
      ERROR("Possibly nonterminating rewrite:\n" ++
            prettyShow p)
    aux n p t =
      case parallel strat t of
        (q:_) | u <- result q, ok u ->
          aux (n+1) (p `trans` q) u
        _ -> p

-- Compute all normal forms of a term wrt a particular strategy.
{-# INLINEABLE normalForms #-}
normalForms :: Function f => Strategy f -> [Reduction f] -> Set (Reduction f)
normalForms strat ps = {-# SCC normalForms #-} go Set.empty Set.empty ps
  where
    go _ norm [] = norm
    go dead norm (p:ps)
      | p `Set.member` dead = go dead norm ps
      | p `Set.member` norm = go dead norm ps
      | null qs = go dead (Set.insert p norm) ps
      | otherwise =
        go (Set.insert p dead) norm (qs ++ ps)
      where
        qs = [ p `Trans` q | q <- anywhere strat (result p) ]

-- Apply a strategy anywhere in a term.
anywhere :: Strategy f -> Strategy f
anywhere strat t = strat t ++ nested (anywhere strat) t

-- Apply a strategy to some child of the root function.
nested :: Strategy f -> Strategy f
nested strat Var{} = []
nested strat (App f ts) =
  cong f <$> inner [] ts
  where
    inner _ Empty = []
    inner before (Cons t u) =
      [ reverse before ++ [p] ++ map Refl (unpack u)
      | p <- strat t ] ++
      inner (Refl t:before) u

-- Apply a strategy in parallel in as many places as possible.
-- Takes only the first rewrite of each strategy.
{-# INLINE parallel #-}
parallel :: PrettyTerm f => Strategy f -> Strategy f
parallel strat t =
  case par t of
    Refl{} -> []
    p -> [p]
  where
    par t | p:_ <- strat t = p
    par (App f ts) = cong f (inner [] ts)
    par t = Refl t

    inner before Empty = reverse before
    inner before (Cons t u) = inner (par t:before) u

--------------------------------------------------------------------------------
-- Basic strategies. These only apply at the root of the term.
--------------------------------------------------------------------------------

-- A strategy which rewrites using an index.
{-# INLINE rewrite #-}
rewrite :: (Function f, Has a (Rule f), Has a VersionedId) => (Rule f -> Subst f -> Bool) -> Index f a -> Strategy f
rewrite p rules t = do
  rule <- Index.approxMatches t rules
  tryRule p rule t

-- A strategy which applies one rule only.
{-# INLINEABLE tryRule #-}
tryRule :: (Function f, Has a (Rule f), Has a VersionedId) => (Rule f -> Subst f -> Bool) -> a -> Strategy f
tryRule p rule t = do
  sub <- maybeToList (match (lhs (the rule)) t)
  guard (p (the rule) sub)
  return (Step (the rule) (the rule) sub)

-- Check if a rule can be applied, given an ordering <= on terms.
{-# INLINEABLE reducesWith #-}
reducesWith :: Function f => (Term f -> Term f -> Bool) -> Rule f -> Subst f -> Bool
reducesWith _ (Rule Oriented _ _) _ = True
reducesWith _ (Rule (WeaklyOriented min ts) _ _) sub =
  -- Be a bit careful here not to build new terms
  -- (reducesWith is used in simplify).
  -- This is the same as:
  --   any (not . isMinimal) (subst sub ts)
  any (not . isMinimal . expand) ts
  where
    expand t@(Var x) = fromMaybe t (Term.lookup x sub)
    expand t = t

    isMinimal (App f Empty) = f == min
    isMinimal _ = False
reducesWith p (Rule (Permutative ts) _ _) sub =
  aux ts
  where
    aux [] = False
    aux ((t, u):ts)
      | t' == u' = aux ts
      | otherwise = p u' t'
      where
        t' = subst sub t
        u' = subst sub u
reducesWith p (Rule Unoriented t u) sub =
  p u' t' && u' /= t'
  where
    t' = subst sub t
    u' = subst sub u

-- Check if a rule can be applied normally.
{-# INLINEABLE reduces #-}
reduces :: Function f => Rule f -> Subst f -> Bool
reduces rule sub = reducesWith lessEq rule sub

-- Check if a rule can be applied and is oriented.
{-# INLINEABLE reducesOriented #-}
reducesOriented :: Function f => Rule f -> Subst f -> Bool
reducesOriented rule sub =
  oriented (orientation rule) && reducesWith undefined rule sub

-- Check if a rule can be applied in various circumstances.
{-# INLINEABLE reducesInModel #-}
reducesInModel :: Function f => Model f -> Rule f -> Subst f -> Bool
reducesInModel cond rule sub =
  reducesWith (\t u -> isJust (lessIn cond t u)) rule sub

{-# INLINEABLE reducesSkolem #-}
reducesSkolem :: Function f => Rule f -> Subst f -> Bool
reducesSkolem rule sub =
  reducesWith (\t u -> lessEq (subst skolemise t) (subst skolemise u)) rule sub
  where
    skolemise = con . skolem

----------------------------------------------------------------------
-- Equational proofs.
----------------------------------------------------------------------

newtype Proof f = Proof [ProofStep f] deriving (Show, Monoid, Generic)

instance PrettyTerm f => Pretty (Proof f) where
  pPrint = pPrintProof (\n -> (Right n, Forwards))

data ProofStep f =
  ProofStep {
    ps_dir :: Direction,
    ps_step :: DirectedProofStep f }
  deriving Show

data Direction = Forwards | Backwards
  deriving (Eq, Ord, Show)

data DirectedProofStep f =
    Reduction (Reduction f)
  | Axiom String (Equation f) (Subst f)
  deriving Show

instance Symbolic (Proof f) where
  type ConstantOf (Proof f) = f

instance Symbolic (ProofStep f) where
  type ConstantOf (ProofStep f) = f
  termsDL (ProofStep _ p) = termsDL p
  subst_ sub (ProofStep dir p) = ProofStep dir (subst_ sub p)

instance Symbolic (DirectedProofStep f) where
  type ConstantOf (DirectedProofStep f) = f
  termsDL (Reduction p) = termsDL p
  termsDL (Axiom _ eq sub) = termsDL eq `mplus` termsDL sub

  subst_ sub (Reduction p) = Reduction (subst_ sub p)
  subst_ sub (Axiom name eq s) = Axiom name eq (subst_ sub s)

stepInitial, stepResult :: ProofStep f -> Term f
stepInitial p = t where t :=: _ = stepEquation p
stepResult p = u where _ :=: u = stepEquation p

stepEquation :: ProofStep f -> Equation f
stepEquation (ProofStep Forwards p) = directedStepEquation p
stepEquation (ProofStep Backwards p) = u :=: t
  where
    t :=: u = directedStepEquation p

directedStepEquation :: DirectedProofStep f -> Equation f
directedStepEquation (Reduction p) = initial p :=: result p
directedStepEquation (Axiom _ (t :=: u) sub) = subst sub t :=: subst sub u

-- Construct a proof from an axiom.
axiomProof :: String -> Equation f -> Proof f
axiomProof name eqn =
  Proof
    [ProofStep Forwards $
      Axiom name eqn $
        fromJust $
        flattenSubst [(x, build (var x)) | x <- vars eqn]]

-- Turn a reduction into a proof.
reductionProof :: Reduction f -> Proof f
reductionProof Refl{} = Proof []
reductionProof p = Proof [ProofStep Forwards (Reduction p)]

-- Turn a proof of t=u into a proof of u=t.
backwards :: Proof f -> Proof f
backwards (Proof ps) = Proof (reverse (map back ps))
  where
    back (ProofStep dir p) = ProofStep (opposite dir) p

opposite :: Direction -> Direction
opposite Forwards = Backwards
opposite Backwards = Forwards

instance Monoid Direction where
  mempty = Forwards
  Backwards `mappend` x = opposite x
  Forwards `mappend` x = x

-- Check a proof for validity, given the initial and final terms.
verifyProof :: PrettyTerm f => Term f -> Term f -> Proof f -> Bool
verifyProof t u (Proof ps) = verify t u ps
  where
    verify t u [] = t == u
    verify t v (p:ps) =
      verifyStep t u p && verify u v ps
      where
        u = stepResult p

    verifyStep t u (ProofStep Forwards p) = verifyDirectedStep t u p
    verifyStep t u (ProofStep Backwards p) = verifyDirectedStep u t p
    verifyDirectedStep t u (Reduction p) = verifyReduction t u p
    verifyDirectedStep t u (Axiom _ (t' :=: u') sub) =
      subst sub t' == t && subst sub u' == u

-- Pretty-print the proof of a single lemma.
pPrintProof :: PrettyTerm f =>
  -- For opportunistically replacing rules.
  (VersionedId -> (Either String VersionedId, Direction)) ->
  Proof f -> Doc
pPrintProof replace (Proof ps) =
  pp (concatMap simplify ps)
  where
    simplify :: ProofStep f -> [ProofStep f]
    simplify (ProofStep dir p) = ProofStep dir <$> simplifyDir p
    simplifyDir (Reduction p) = Reduction <$> flatten p
    simplifyDir p@Axiom{} = [p]

    -- Transform each reduction so it only uses Step, Cong and Refl,
    -- and no top-level Refls.
    flatten Refl{} = []
    flatten (Trans p q) = flatten p ++ flatten q
    flatten (Cong f ps) = map (cong f) (transpose (flattenPad ps))
    flatten p@Step{} = [p]

    -- Given a list of (unrelated) reductions, flatten each of them,
    -- making each flattened reduction have the same length
    -- (by padding with Refl)..
    flattenPad ps =
      map (take (maximum (0:map length pss))) $
      zipWith pad ps pss
      where
        pad p ps = ps ++ repeat (Refl (result p))
        pss = map flatten ps

    pp [] = text "reflexivity"
    pp ps@(p0:_) =
      vcat $
        ppTerm (stepInitial p0):
        [ text "= { by" <+> ppStep p <+> text "}" $$
          ppTerm (stepResult p)
        | p <- ps ]

    ppTerm t = text "  " <> pPrint t

    ppStep (ProofStep dir p) =
      hcat (punctuate "; " (map ppGroup groups))
      where
        used = [ (x, dir `mappend` dir') | (x, dir') <- usort (findSteps p) ]
        groups = partitionBy (\(x, dir) -> (isRight x, dir)) used

    ppGroup group@((rule, dir):_) =
      text (if isLeft rule then "axiom" else "rule") <>
      text (if length group > 1 then "s" else "") <+>
      hcat (punctuate (text ", ") (map ppLaw (init group))) <+>
      ppLaw (last group) <>
      case dir of
        Forwards -> text ""
        Backwards -> text " backwards"
      where
        ppLaw (Left name, _) = text name
        ppLaw (Right n, _) = pPrint n

    findSteps (Axiom name _ _) = [(Left name, Forwards)]
    findSteps (Reduction p) = [replace n | (n, _, _) <- steps p]

-- Pretty-print a complete proof.
pPrintTheorem ::
  forall f a. (PrettyTerm f, Has a (Proof f), Has a (Rule f)) =>
  Map VersionedId a ->
  [(String, Equation f, Proof f)] ->
  String
pPrintTheorem rules goals =
  unlines $ intercalate [""] $
    [ pp ("Lemma " ++ prettyShow n) (unorient (the rule)) (the rule)
    | n <- Set.toList usedRules,
      let rule = fromJust (Map.lookup n rules)] ++
    [ pp ("Goal " ++ name) eqn proof
    | (name, eqn, proof) <- goals ]
  where
    pp title eqn p =
      let
        repl n = replace (unorient (the (fromJust (Map.lookup n rules)))) in
      [ title ++ ": " ++ prettyShow eqn ++ ".",
        "Proof:" ] ++
      lines (show (pPrintProof repl p))

    -- Compute which rules are used in the proof.
    usedRules :: Set VersionedId
    usedRules =
      usedRulesFrom Set.empty
        (concat [proofRules proof | (_, _, proof) <- goals])

    usedRulesFrom used [] = used
    usedRulesFrom used ((n, eqn):xs) =
      case replace eqn of
        (Right n, _) ->
          usedRulesFrom (Set.insert n used)
          (proofRules (the (fromJust (Map.lookup n rules))) ++ xs)
        (Left _, _) ->
          usedRulesFrom used xs

    proofRules :: Proof f -> [(VersionedId, Equation f)]
    proofRules (Proof ps) =
      usort $
      [ (n, unorient rule)
      | ProofStep _ (Reduction p) <- ps,
        (n, rule, _) <- steps p ]

    -- Replace a rule with an equivalent rule or an axiom.
    replace :: Equation f -> (Either String VersionedId, Direction)
    replace eqn =
      let
        (n, dir) =
          fromJust (Map.lookup eqn equations)
      in
        case Map.lookup n axioms of
          Nothing -> (Right n, dir)
          Just (ax, dir') -> (Left ax, dir `mappend` dir')

    -- Rules whose proofs are just a single axiom.
    axioms :: Map VersionedId (String, Direction)
    axioms =
      Map.mapMaybe
        (\rule ->
           case the rule :: Proof f of
             Proof [ProofStep dir (Axiom name _ _)] -> Just (name, dir)
             _ -> Nothing)
        rules

    -- For each equation, the earliest rule which proves that equation.
    equations :: Map (Equation f) (VersionedId, Direction)
    equations =
      Map.fromListWith min $ concat
        [ [(t :=: u, (n, Forwards)), (u :=: t, (n, Backwards))]
        | (n, rule) <- Map.toList rules,
          let t = lhs (the rule)
              u = rhs (the rule) ]
