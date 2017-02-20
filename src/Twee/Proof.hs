{-# LANGUAGE TypeFamilies, PatternGuards, RecordWildCards, ScopedTypeVariables #-}
module Twee.Proof(
  Proof, Derivation(..), Lemma(..), Axiom(..),
  certify, equation, derivation,
  lemma, axiom, symm, trans, cong, simplify, usedLemmas, usedAxioms,
  Presentation(..), ProvedGoal(..), goalWitness, present, describeEquation) where

import Twee.Base
import Twee.Equation
import Twee.Utils
import Control.Monad
import Data.Maybe
import Data.List
import qualified Data.Map.Strict as Map
import qualified Text.PrettyPrint as PP

----------------------------------------------------------------------
-- Equational proofs. Only valid proofs can be constructed.
----------------------------------------------------------------------

-- A checked proof. If you have a value of type Proof f,
-- it should jolly well represent a valid proof!
data Proof f =
  Proof {
    equation   :: !(Equation f),
    derivation :: !(Derivation f) }
  deriving Show

-- A derivation is an unchecked proof. It might be wrong!
-- The way to check it is to call "certify" to turn it into a Proof.
data Derivation f =
    -- Apply an existing rule (with proof!) to the root of a term
    UseLemma {-# UNPACK #-} !(Lemma f) !(Subst f)
    -- Apply an axiom to the root of a term
  | UseAxiom {-# UNPACK #-} !(Axiom f) !(Subst f)
    -- Reflexivity
  | Refl !(Term f)
    -- Symmetry
  | Symm !(Derivation f)
    -- Transivitity
  | Trans !(Derivation f) !(Derivation f)
    -- Congruence
  | Cong {-# UNPACK #-} !(Fun f) ![Derivation f]
  deriving Show

-- A lemma, which includes a proof.
data Lemma f =
  Lemma {
    lemma_id :: {-# UNPACK #-} !VersionedId,
    lemma_proof :: !(Proof f) }
  deriving Show

-- An axiom, which comes without proof.
data Axiom f =
  Axiom {
    axiom_number :: {-# UNPACK #-} !Int,
    axiom_name :: !String,
    axiom_eqn :: !(Equation f) }
  deriving (Eq, Ord, Show)

-- The trusted core of the module.
-- Turns a derivation into a proof, while checking the derivation.
certify :: Derivation f -> Proof f
certify p =
  {-# SCC certify #-}
  case check p of
    Nothing -> error ("Invalid proof created!\n" ++ show p)
    Just eqn -> Proof eqn p
  where
    check (UseLemma Lemma{..} sub) =
      return (subst sub (equation lemma_proof))
    check (UseAxiom Axiom{..} sub) =
      return (subst sub axiom_eqn)
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
  termsDL (UseLemma _ sub) = termsDL sub
  termsDL (UseAxiom _ sub) = termsDL sub
  termsDL (Refl t) = termsDL t
  termsDL (Symm p) = termsDL p
  termsDL (Trans p q) = termsDL p `mplus` termsDL q
  termsDL (Cong _ ps) = termsDL ps

  subst_ sub (UseLemma lemma s) = UseLemma lemma (subst_ sub s)
  subst_ sub (UseAxiom axiom s) = UseAxiom axiom (subst_ sub s)
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
    simp p@(UseLemma lemma sub) =
      case lem lemma of
        Nothing -> p
        Just q -> simp (subst sub q)
    simp (Symm p) = symm (simp p)
    simp (Trans p q) = trans (simp p) (simp q)
    simp (Cong f ps) = cong f (map simp ps)
    simp p = p

-- Smart constructors for derivations.
lemma :: Lemma f -> Subst f -> Derivation f
lemma lem@Lemma{..} sub = UseLemma lem sub

axiom :: Axiom f -> Derivation f
axiom ax@Axiom{..} =
  UseAxiom ax $
    fromJust $
    flattenSubst [(x, build (var x)) | x <- vars axiom_eqn]

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
    lem (UseLemma lemma _) = (lemma:)
    lem (Symm p) = lem p
    lem (Trans p q) = lem p . lem q
    lem (Cong _ ps) = foldr (.) id (map lem ps)
    lem _ = id

-- Find all axioms which are used in a derivation.
usedAxioms :: Derivation f -> [Axiom f]
usedAxioms p = lem p []
  where
    lem (UseAxiom axiom _) = (axiom:)
    lem (Symm p) = lem p
    lem (Trans p q) = lem p . lem q
    lem (Cong _ ps) = foldr (.) id (map lem ps)
    lem _ = id

----------------------------------------------------------------------
-- Pretty-printing of proofs.
----------------------------------------------------------------------

-- A proof, with all axioms and lemmas explicitly listed.
data Presentation f =
  Presentation {
    pres_axioms :: [Axiom f],
    pres_lemmas :: [Lemma f],
    pres_goals  :: [ProvedGoal f] }
  deriving Show

data ProvedGoal f =
  ProvedGoal {
    pg_number :: Int,
    pg_name   :: String,
    pg_proof  :: Proof f }
  deriving Show

instance Function f => Pretty (Presentation f) where
  pPrint = pPrintPresentation

present :: PrettyTerm f => [ProvedGoal f] -> Presentation f
present goals =
  -- First find all the used lemmas, then hand off to presentWithGoals
  presentWithGoals goals
    (used Map.empty (concatMap (usedLemmas . derivation . pg_proof) goals))
  where
    used lems [] = Map.elems lems
    used lems (lem@(Lemma n p):xs)
      | n `Map.member` lems = used lems xs
      | otherwise =
        used (Map.insert n lem lems)
          (usedLemmas (derivation p) ++ xs)

presentWithGoals ::
  PrettyTerm f =>
  [ProvedGoal f] -> [Lemma f] -> Presentation f
presentWithGoals goals lemmas
  -- We inline a lemma if one of the following holds:
  --   * It only has one step
  --   * It is subsumed by an earlier lemma
  --   * It is only used once, and that use is at the root of the term
  -- First we compute all inlinings, then apply simplify to remove them,
  -- then repeat if any lemma was inlined
  | Map.null inlinings =
    let
      axioms = usort $
        concatMap (usedAxioms . derivation . pg_proof) goals ++
        concatMap (usedAxioms . derivation . lemma_proof) lemmas
    in
      Presentation axioms lemmas goals

  | otherwise =
    let
      inline Lemma{..} = Map.lookup lemma_id inlinings

      goals' =
        [ goal { pg_proof = certify $ simplify inline (derivation pg_proof) }
        | goal@ProvedGoal{..} <- goals ]
      lemmas' =
        [ Lemma n (certify $ simplify inline (derivation p))
        | Lemma n p <- lemmas, not (n `Map.member` inlinings) ]
    in
      presentWithGoals goals' lemmas'

  where
    inlinings =
      Map.fromList
        [ (lemma_id, p)
        | lemma@Lemma{..} <- lemmas, Just p <- [tryInline lemma]]

    tryInline (Lemma n p)
      | oneStep (derivation p) = Just (derivation p)
      | Map.lookup n uses == Just 1,
        Map.lookup n usesAtRoot == Just 1 = Just (derivation p)
    tryInline (Lemma n p)
      -- Check for subsumption by an earlier lemma
      | Just (Lemma m q) <- Map.lookup (canonicalise (t :=: u)) equations, m < n =
        Just (subsume p (derivation q))
      | Just (Lemma m q) <- Map.lookup (canonicalise (u :=: t)) equations, m < n =
        Just (subsume p (Symm (derivation q)))
      where
        t :=: u = equation p
    tryInline _ = Nothing

    subsume p q =
      -- Rename q so its variables match p's
      subst sub q
      where
        t  :=: u  = equation p
        t' :=: u' = equation (certify q)
        Just sub  = matchList (buildList [t', u']) (buildList [t, u])

    -- Record which lemma proves each equation
    equations =
      Map.fromList
        [ (canonicalise (equation lemma_proof), lemma)
        | lemma@Lemma{..} <- lemmas]

    -- Count how many times each lemma is used at the root
    uses = usesWith usedLemmas
    usesAtRoot = usesWith rootLemmas
    usesWith lem =
      Map.fromListWith (+)
        [ (lemma_id, 1)
        | Lemma{..} <-
            concatMap lem
              (map (derivation . pg_proof) goals ++
               map (derivation . lemma_proof) lemmas) ]

    -- Find all lemmas that occur at the root
    rootLemmas (UseLemma lemma _) = [lemma]
    rootLemmas (Symm p) = rootLemmas p
    rootLemmas (Trans p q) = rootLemmas p ++ rootLemmas q
    rootLemmas _ = []

    -- Check if a proof only has one step.
    -- Trans only occurs at the top level by this point.
    oneStep Trans{} = False
    oneStep _ = True

-- Pretty-print the proof of a single lemma.
pPrintLemma :: PrettyTerm f => (VersionedId -> String) -> Proof f -> Doc
pPrintLemma lemmaName p =
  ppTerm (eqn_lhs (equation p)) $$ pp q
  where
    q = floatTrans (simplify (const Nothing) (derivation p))

    -- Lift Trans outside of Cong, so that each Cong only
    -- uses one lemma or axiom.
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
      (text "= { by" <+>
       ppStep
         (nub (map showLemma (usedLemmas p)) ++
          nub (map showAxiom (usedAxioms p))) <+>
       text "}" $$
       ppTerm (eqn_rhs (equation (certify p))))

    ppTerm t = text "  " <> pPrint t

    ppStep [] = text "reflexivity" -- ??
    ppStep [x] = text x
    ppStep xs =
      hcat (punctuate (text ", ") (map text (init xs))) <+>
      text "and" <+>
      text (last xs)

    showLemma Lemma{..} = "lemma " ++ lemmaName lemma_id
    showAxiom Axiom{..} =
      "axiom " ++ show axiom_number ++ " (" ++ axiom_name ++ ")"

pPrintPresentation :: forall f. Function f => Presentation f -> Doc
pPrintPresentation (Presentation axioms lemmas goals) =
  vcat $ intersperse (text "") $
    vcat [ text (describeEquation "Axiom" (show n) (Just name) eqn)
         | Axiom n name eqn <- axioms ]:
    [ pp "Lemma" (num n) Nothing p
    | Lemma n p <- lemmas ] ++
    [ pp "Goal" (show num) (Just pg_name) pg_proof $$
      ppWitness goal
    | (num, goal@ProvedGoal{..}) <- zip [1..] goals ]
  where
    pp kind n mname p =
      text (describeEquation kind n mname (equation p)) $$
      text "Proof:" $$
      pPrintLemma num p

    num x = show (fromJust (Map.lookup x nums))
    nums = Map.fromList (zip (map lemma_id lemmas) [n+1 ..])
    n = maximum $ 0:map axiom_number axioms

    ppWitness goal =
      case goalWitness goal of
        Nothing -> PP.empty
        Just (eqn, sub) ->
          vcat [
            text "",
            text "The conjecture",
            nest 2 (pPrint eqn),
            text "is true when:",
            nest 2 $ vcat
              [ pPrint x <+> text "=" <+> pPrint t
              | (x, t) <- listSubst sub ],
            if minimal `elem` funs (eqn, sub) then
              text "where" <+> doubleQuotes (pPrint (minimal :: Fun f)) <+>
              text "stands for an arbitrary term of your choosing."
            else PP.empty]

-- Format an equation nicely. Used both here and in the main file.
describeEquation ::
  PrettyTerm f =>
  String -> String -> Maybe String -> Equation f -> String
describeEquation kind num mname eqn =
  prettyShow $
  text kind <+> text num <>
  (case mname of
     Nothing -> text ""
     Just name -> text (" (" ++ name ++ ")")) <>
  text ":" <+> pPrint eqn <> text "."

-- Try to find a witness for a proof of an existentially-quantified
-- formula, given the proof of $true = $false.
goalWitness :: Function f => ProvedGoal f -> Maybe (Equation f, Subst f)
goalWitness ProvedGoal{..}
  -- The idea: in a proof $true = $false, the very last step
  -- (if we also expand lemmas) must be an application of an
  -- axiom $equals(..) = $false. (This is because these are the
  -- only axioms which mention $false.)
  --
  -- All we have to do is pick out the substitution from that step.
  --
  -- To make this work, we first simplify the proof, in order to:
  --   a) expand any lemma which proves ... = $false
  --      (strictly speaking we need only do this if this lemma
  --      is the last step of the proof);
  --   b) make sure that the proof doesn't end in a Refl.
  | u == false = extract deriv
    -- Orient the equation so that $false is the RHS.
  | t == false = extract (symm deriv)
  | otherwise = Nothing
  where
    t :=: u = equation pg_proof
    deriv =
      derivation $ certify $ -- double-check the proof just to be sure
      simplify simp (derivation pg_proof)

    simp Lemma{..} = do
      guard $
        eqn_rhs (equation lemma_proof) == false ||
        eqn_lhs (equation lemma_proof) == false

      return (derivation lemma_proof)

    -- Here we can assume that the lemma ends in an axiom
    -- $equals(..) = $false.
    extract (Trans _ p) = extract p
    extract (UseAxiom Axiom{axiom_eqn = t :=: u} sub) = do
      eqn <- getEquals t
      guard (u == false)
      guard (substSize sub /= 0)
      return (eqn, sub)
    extract _ = Nothing

    false = build (con falseCon)
    getEquals (App equals (Cons t (Cons u Empty)))
      | equals == equalsCon = Just (t :=: u)
    getEquals _ = Nothing
