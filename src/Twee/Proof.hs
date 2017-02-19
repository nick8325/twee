{-# LANGUAGE TypeFamilies, PatternGuards #-}
module Twee.Proof(
  Proof, equation, derivation, Derivation(..), Lemma(..),
  certify, lemmaEquation,
  simplify, step, symm, trans, cong,
  pPrintLemma, pPrintTheorem) where

import Twee.Base
import Twee.Equation
import Control.Monad
import Data.Maybe
import Data.List
import Data.Function
import qualified Data.Map.Strict as Map
import Data.Map(Map)

----------------------------------------------------------------------
-- Equational proofs. Only valid proofs can be constructed.
----------------------------------------------------------------------

-- A checked proof. If you have a value of type Proof f,
-- it should jolly well represent a valid proof!
data Proof f =
  Proof {
    equation   :: {-# UNPACK #-} !(Equation f),
    derivation :: !(Derivation f) }
  deriving Show

-- A derivation is an unchecked proof. It might be wrong!
-- The way to check it is to call "certify" to turn it into a Proof.
data Derivation f =
    -- Apply a single rule or axiom to the root of a term
    Step !(Lemma f) !(Subst f)
    -- Reflexivity
  | Refl {-# UNPACK #-} !(Term f)
    -- Symmetry
  | Symm !(Derivation f)
    -- Transivitity
  | Trans !(Derivation f) !(Derivation f)
    -- Congruence
  | Cong {-# UNPACK #-} !(Fun f) ![Derivation f]
  deriving Show

-- The source of a proof step. Either an existing rule (with proof)!
-- or an axiom.
data Lemma f =
    Rule {-# UNPACK #-} !VersionedId !(Proof f)
  | Axiom !String !(Equation f)
  deriving Show

-- What equation does a lemma prove?
lemmaEquation :: Lemma f -> Equation f
lemmaEquation (Rule _ p) = equation p
lemmaEquation (Axiom _ eqn) = eqn

-- The trusted core of the module.
-- Turns a derivation into a proof, while checking the derivation.
certify :: Derivation f -> Proof f
certify p =
  case check p of
    Nothing -> error ("Invalid proof created!\n" ++ show p)
    Just eqn -> Proof eqn p
  where
    check (Step lemma sub) =
      return (subst sub (lemmaEquation lemma))
    check (Refl t) =
      return (t :=: t)
    check (Symm p) = do
      t :=: u <- check p
      return (u :=: t)
    check (Trans p q) = do
      t :=: u1 <- check p
      u2 :=: v <- check q
      guard (u1 == u2)
      return (t :=: v)
    check (Cong f ps) = do
      eqns <- mapM check ps
      return
        (build (app f (map eqn_lhs eqns)) :=:
         build (app f (map eqn_rhs eqns)))

----------------------------------------------------------------------
-- Everything below this point need not be trusted, since all proof
-- construction goes through the "proof" function.
----------------------------------------------------------------------

-- Typeclass instances.
instance Symbolic (Derivation f) where
  type ConstantOf (Derivation f) = f
  termsDL (Step _ sub) = termsDL sub
  termsDL (Refl t) = termsDL t
  termsDL (Symm p) = termsDL p
  termsDL (Trans p q) = termsDL p `mplus` termsDL q
  termsDL (Cong _ ps) = termsDL ps

  subst_ sub (Step lemma s) = Step lemma (subst_ sub s)
  subst_ sub (Refl t) = Refl (subst_ sub t)
  subst_ sub (Symm p) = symm (subst_ sub p)
  subst_ sub (Trans p q) = trans (subst_ sub p) (subst_ sub q)
  subst_ sub (Cong f ps) = cong f (subst_ sub ps)

instance PrettyTerm f => Pretty (Proof f) where pPrint = pPrintLemma prettyShow
instance PrettyTerm f => Pretty (Derivation f) where pPrint = pPrint . certify

-- Simplify a derivation.
-- After simplification, a derivation has the following properties:
--   * Trans is right-associated and only appears at the top level
--   * Symm is pushed down next to Step
--   * Each Cong only does one rewrite (i.e. contains one Step constructor)
--   * Refl only occurs inside Cong
simplify :: (Lemma f -> Maybe (Derivation f)) -> Derivation f -> Derivation f
simplify lem p = simp p
  where
    simp p@(Step lemma sub) =
      case lem lemma of
        Nothing -> p
        Just q -> simp (subst sub q)
    simp p@Refl{} = p
    simp (Symm p) = symm (simp p)
    simp (Trans p q) = trans (simp p) (simp q)
    simp (Cong f ps) = cong f (map simp ps)

-- Smart constructors for derivations.
step :: Lemma f -> Derivation f
step lemma =
  Step lemma $
    fromJust $
    flattenSubst [(x, build (var x)) | x <- lemmaVars lemma]
  where
    lemmaVars = vars . eqn_lhs . lemmaEquation

symm :: Derivation f -> Derivation f
symm (Refl t) = Refl t
symm (Symm p) = p
symm (Trans p q) = trans (symm q) (symm p)
symm (Cong f ps) = cong f (map symm ps)
symm p = Symm p

trans :: Derivation f -> Derivation f -> Derivation f
trans Refl{} p = p
trans p Refl{} = p
trans (Trans p q) r =
  -- Right-associate uses of transitivity.
  -- p cannot be a Trans (if it was created with the smart
  -- constructors) but q could be.
  Trans p (trans q r)
-- Collect adjacent uses of congruence.
trans (Cong f ps) (Cong g qs) | f == g =
  transCong f ps qs
trans (Cong f ps) (Trans (Cong g qs) r) | f == g =
  trans (transCong f ps qs) r
trans p q = Trans p q

transCong :: Fun f -> [Derivation f] -> [Derivation f] -> Derivation f
transCong f ps qs =
  cong f (zipWith trans ps qs)

cong :: Fun f -> [Derivation f] -> Derivation f
cong f ps =
  case sequence (map unRefl ps) of
    Nothing -> Cong f ps
    Just ts -> Refl (build (app f ts))
  where
    unRefl (Refl t) = Just t
    unRefl _ = Nothing

-- Find all lemmas which are used in a derivation.
usedLemmas :: Derivation f -> [Lemma f]
usedLemmas p = lem p []
  where
    lem (Step lemma _) = (lemma:)
    lem Refl{} = id
    lem (Symm p) = lem p
    lem (Trans p q) = lem p . lem q
    lem (Cong _ ps) = foldr (.) id (map lem ps)

-- Pretty-print the proof of a single lemma.
pPrintLemma :: PrettyTerm f => (VersionedId -> String) -> Proof f -> Doc
pPrintLemma lemmaName p =
  ppTerm (eqn_lhs (equation p)) $$ pp q
  where
    q = floatTrans (simplify (const Nothing) (derivation p))

    -- Lift Trans outside of Cong, so that each Cong only
    -- uses one Step constructor.
    floatTrans :: Derivation f -> Derivation f
    floatTrans (Symm p) = Symm (floatTrans p)
    floatTrans (Trans p q) = Trans (floatTrans p) (floatTrans q)
    floatTrans (Cong f ps)
      | any isTrans ps =
        Cong f (map fst peeled) `Trans`
        floatTrans (Cong f (map snd peeled))
      where
        peeled = map peel ps
        peel (Trans p q) = (p, q)
        peel p = (p, Refl (eqn_rhs (equation (certify p))))

        isTrans Trans{} = True
        isTrans _ = False
    floatTrans p = p

    pp (Trans p q) = pp p $$ pp q
    pp p =
      (text "= { by" <+> ppStep (nub (map showLemma (usedLemmas p))) <+> text "}" $$
       ppTerm (eqn_rhs (equation (certify p))))

    ppTerm t = text "  " <> pPrint t

    ppStep [] = text "reflexivity" -- ??
    ppStep [x] = text x
    ppStep xs =
      hcat (punctuate (text ", ") (map text (init xs))) <+>
      text "and" <+>
      text (last xs)

    showLemma (Rule n _) = "lemma " ++ lemmaName n
    showLemma (Axiom name _) = "axiom " ++ name

-- Pretty-print a complete proof.
pPrintTheorem :: PrettyTerm f => [(String, Proof f)] -> String
pPrintTheorem goals =
  -- First find all the used lemmas, then hand off to pPrintGoalsAndLemmas
  pPrintGoalsAndLemmas goals (used Map.empty (concatMap (rules . snd) goals))
  where
    used ps [] = ps
    used ps ((n, p):xs)
      | n `Map.member` ps = used ps xs
      | otherwise =
        used (Map.insert n p ps) (rules p ++ xs)
    rules x =
      [ (n, p) | Rule n p <- usedLemmas (derivation x) ]

pPrintGoalsAndLemmas ::
  PrettyTerm f =>
  [(String, Proof f)] -> Map VersionedId (Proof f) -> String
pPrintGoalsAndLemmas goals lemmas
  -- We inline a lemma if one of the following holds:
  --   * It only has one step
  --   * It is subsumed by an earlier lemma
  --   * It is only used once, and that use is at the root of the term
  -- First we compute all inlinings, then apply simplify to remove them,
  -- then repeat if any lemma was inlined
  | Map.null inlinings = pPrintFinalGoalsAndLemmas goals lemmas
  | otherwise =
    let
      inline (Rule n _) = Map.lookup n inlinings
      inline Axiom{} = Nothing

      goals' =
        [ (name, certify $ simplify inline (derivation p))
        | (name, p) <- goals ]
      lemmas' =
        Map.fromList
        [ (n, certify $ simplify inline (derivation p))
        | (n, p) <- Map.toList lemmas,
          not (n `Map.member` inlinings) ]
    in
      pPrintGoalsAndLemmas goals' lemmas'

  where
    inlinings =
      Map.mapMaybeWithKey tryInline lemmas

    tryInline n p
      | oneStep (derivation p) = Just (derivation p)
      | Map.lookup n uses == Just 1,
        Map.lookup n usesAtRoot == Just 1 = Just (derivation p)
    tryInline n p
      -- Check for subsumption by an earlier lemma
      | Just (m, q) <- Map.lookup (t :=: u) equations, m < n =
        Just q
      | Just (m, q) <- Map.lookup (u :=: t) equations, m < n =
        Just (Symm q)
      where
        t :=: u = equation p
    tryInline _ _ = Nothing

    -- Record which lemma proves each equation
    equations =
      Map.fromList
        [ (equation p, (n, step (Rule n p)))
        | (n, p) <- Map.toList lemmas]

    -- Count how many times each lemma is used at the root
    uses = usesWith usedLemmas
    usesAtRoot = usesWith lemmasAtRoot
    usesWith lem =
      Map.fromListWith (+)
        [ (n, 1)
        | Rule n _ <-
            concatMap lem
              (map (derivation . snd) goals ++
               map derivation (Map.elems lemmas)) ]

    -- Find all lemmas that occur at the root
    lemmasAtRoot (Step lemma _) = [lemma]
    lemmasAtRoot (Symm p) = lemmasAtRoot p
    lemmasAtRoot (Trans p q) = lemmasAtRoot p ++ lemmasAtRoot q
    lemmasAtRoot _ = []

    -- Check if a proof only has one step.
    -- Trans only occurs at the top level by this point.
    oneStep Trans{} = False
    oneStep _ = True

pPrintFinalGoalsAndLemmas ::
  PrettyTerm f =>
  [(String, Proof f)] -> Map VersionedId (Proof f) -> String
pPrintFinalGoalsAndLemmas goals lemmas =
  unlines $ intercalate [""] $
    [ pp ("Lemma " ++ num x) p
    | (x, p) <- Map.toList lemmas ] ++
    [ pp ("Goal " ++ name) p
    | (name, p) <- goals ]
  where
    pp title p =
      [ title ++ ": " ++ prettyShow (equation p) ++ ".",
        "Proof:" ] ++
      lines (show (pPrintLemma num p))

    num x = show (fromJust (Map.lookup x nums))
    nums = Map.fromList (zip (Map.keys lemmas) [1..])
