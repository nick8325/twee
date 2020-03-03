-- | Equational proofs which are checked for correctedness.
{-# LANGUAGE TypeFamilies, PatternGuards, RecordWildCards, ScopedTypeVariables #-}
module Twee.Proof(
  -- * Constructing proofs
  Proof, Derivation(..), Axiom(..),
  certify, equation, derivation,
  -- ** Smart constructors for derivations
  lemma, axiom, symm, trans, cong, congPath,

  -- * Analysing proofs
  simplify, usedLemmas, usedAxioms, usedLemmasAndSubsts, usedAxiomsAndSubsts,
  groundAxiomsAndSubsts,

  -- * Pretty-printing proofs
  Config(..), defaultConfig, Presentation(..),
  ProvedGoal(..), provedGoal, checkProvedGoal,
  pPrintPresentation, present, describeEquation) where

import Twee.Base hiding (invisible)
import Twee.Equation
import Twee.Utils
import Control.Monad
import Data.Maybe
import Data.List
import Data.Ord
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

----------------------------------------------------------------------
-- Equational proofs. Only valid proofs can be constructed.
----------------------------------------------------------------------

-- | A checked proof. If you have a value of type @Proof f@,
-- it should jolly well represent a valid proof!
--
-- The only way to construct a @Proof f@ is by using 'certify'.
data Proof f =
  Proof {
    equation   :: !(Equation f),
    derivation :: !(Derivation f) }
  deriving Show

-- | A derivation is an unchecked proof. It might be wrong!
-- The way to check it is to call 'certify' to turn it into a 'Proof'.
data Derivation f =
    -- | Apply an existing rule (with proof!) to the root of a term
    UseLemma {-# UNPACK #-} !(Proof f) !(Subst f)
    -- | Apply an axiom to the root of a term
  | UseAxiom {-# UNPACK #-} !(Axiom f) !(Subst f)
    -- | Reflexivity. @'Refl' t@ proves @t = t@.
  | Refl !(Term f)
    -- | Symmetry
  | Symm !(Derivation f)
    -- | Transivitity
  | Trans !(Derivation f) !(Derivation f)
    -- | Congruence.
    -- Parallel, i.e., takes a function symbol and one derivation for each
    -- argument of that function.
  | Cong {-# UNPACK #-} !(Fun f) ![Derivation f]
  deriving (Eq, Show)

--  | An axiom, which comes without proof.
data Axiom f =
  Axiom {
    -- | The number of the axiom.
    -- Has no semantic meaning; for convenience only.
    axiom_number :: {-# UNPACK #-} !Int,
    -- | A description of the axiom.
    -- Has no semantic meaning; for convenience only.
    axiom_name :: !String,
    -- | The equation which the axiom asserts.
    axiom_eqn :: !(Equation f) }
  deriving (Eq, Ord, Show)

-- | Checks a 'Derivation' and, if it is correct, returns a
-- certified 'Proof'.
--
-- If the 'Derivation' is incorrect, throws an exception.

-- This is the trusted core of the module.
{-# INLINEABLE certify #-}
certify :: PrettyTerm f => Derivation f -> Proof f
certify p =
  {-# SCC certify #-}
  case check p of
    Nothing -> error ("Invalid proof created!\n" ++ prettyShow p)
    Just eqn -> Proof eqn p
  where
    check (UseLemma proof sub) =
      return (subst sub (equation proof))
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
-- construction goes through the "certify" function.
--
-- N.B.: For this reason, the code below must never directly invoke
-- the Proof constructor!
----------------------------------------------------------------------

-- Typeclass instances.
instance Eq (Proof f) where
  x == y = compare x y == EQ
instance Ord (Proof f) where
  -- Don't look at the proof itself, to prevent exponential blowup
  -- when a proof contains UseLemma
  compare = comparing equation

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

instance Function f => Pretty (Proof f) where
  pPrint = pPrintLemma defaultConfig (prettyShow . axiom_number) (prettyShow . equation)
instance PrettyTerm f => Pretty (Derivation f) where
  pPrint (UseLemma lemma sub) =
    text "subst" <#> pPrintTuple [text "lemma" <#> pPrint (equation lemma), pPrint sub]
  pPrint (UseAxiom axiom sub) =
    text "subst" <#> pPrintTuple [pPrint axiom, pPrint sub]
  pPrint (Refl t) =
    text "refl" <#> pPrintTuple [pPrint t]
  pPrint (Symm p) =
    text "symm" <#> pPrintTuple [pPrint p]
  pPrint (Trans p q) =
    text "trans" <#> pPrintTuple [pPrint p, pPrint q]
  pPrint (Cong f ps) =
    text "cong" <#> pPrintTuple (pPrint f:map pPrint ps)

instance PrettyTerm f => Pretty (Axiom f) where
  pPrint Axiom{..} =
    text "axiom" <#>
    pPrintTuple [pPrint axiom_number, text axiom_name, pPrint axiom_eqn]

-- | Simplify a derivation.
--
-- After simplification, a derivation has the following properties:
--
--   * 'Symm' is pushed down next to 'Lemma' and 'Axiom'
--   * 'Refl' only occurs inside 'Cong' or at the top level
--   * 'Trans' is right-associated and is pushed inside 'Cong' if possible
simplify :: Minimal f => (Proof f -> Maybe (Derivation f)) -> Derivation f -> Derivation f
simplify lem p = simp p
  where
    simp p@(UseLemma q sub) =
      case lem q of
        Nothing -> p
        Just r ->
          let
            -- Get rid of any variables that are not bound by sub
            -- (e.g., ones which only occur internally in q)
            dead = usort (vars r) \\ substDomain sub
          in simp (subst sub (erase dead r))
    simp (Symm p) = symm (simp p)
    simp (Trans p q) = trans (simp p) (simp q)
    simp (Cong f ps) = cong f (map simp ps)
    simp p = p

lemma :: Proof f -> Subst f -> Derivation f
lemma p sub = UseLemma p sub

axiom :: Axiom f -> Derivation f
axiom ax@Axiom{..} =
  UseAxiom ax $
    fromJust $
    listToSubst [(x, build (var x)) | x <- vars axiom_eqn]

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

-- | Find all lemmas which are used in a derivation.
usedLemmas :: Derivation f -> [Proof f]
usedLemmas p = map fst (usedLemmasAndSubsts p)

-- | Find all lemmas which are used in a derivation,
-- together with the substitutions used.
usedLemmasAndSubsts :: Derivation f -> [(Proof f, Subst f)]
usedLemmasAndSubsts p = lem p []
  where
    lem (UseLemma p sub) = ((p, sub):)
    lem (Symm p) = lem p
    lem (Trans p q) = lem p . lem q
    lem (Cong _ ps) = foldr (.) id (map lem ps)
    lem _ = id

-- | Find all axioms which are used in a derivation.
usedAxioms :: Derivation f -> [Axiom f]
usedAxioms p = map fst (usedAxiomsAndSubsts p)

-- | Find all axioms which are used in a derivation,
-- together with the substitutions used.
usedAxiomsAndSubsts :: Derivation f -> [(Axiom f, Subst f)]
usedAxiomsAndSubsts p = ax p []
  where
    ax (UseAxiom axiom sub) = ((axiom, sub):)
    ax (Symm p) = ax p
    ax (Trans p q) = ax p . ax q
    ax (Cong _ ps) = foldr (.) id (map ax ps)
    ax _ = id

-- | Find all axioms which are used in the grounded form
-- of a derivation (no lemmas).
groundAxiomsAndSubsts :: Derivation f -> [(Axiom f, Subst f)]
groundAxiomsAndSubsts p = ax emptySubst p []
  where
    ax sub1 (UseAxiom axiom sub2) = ((axiom, substCompose sub1 sub2):)
    ax sub1 (UseLemma lemma sub2) = ax (substCompose sub1 sub2) (derivation lemma)
    ax sub  (Symm p) = ax sub p
    ax sub  (Trans p q) = ax sub p . ax sub q
    ax sub  (Cong _ ps) = foldr (.) id (map (ax sub) ps)
    ax _    _           = id

-- | Applies a derivation at a particular path in a term.
congPath :: [Int] -> Term f -> Derivation f -> Derivation f
congPath [] _ p = p
congPath (n:ns) (App f t) p | n <= length ts =
  cong f $
    map Refl (take n ts) ++
    [congPath ns (ts !! n) p] ++
    map Refl (drop (n+1) ts)
  where
    ts = unpack t
congPath _ _ _ = error "bad path"

----------------------------------------------------------------------
-- Pretty-printing of proofs.
----------------------------------------------------------------------

-- | Options for proof presentation.
data Config =
  Config {
    -- | Never inline lemmas.
    cfg_all_lemmas :: !Bool,
    -- | Inline all lemmas.
    cfg_no_lemmas :: !Bool,
    -- | Print out explicit substitutions.
    cfg_show_instances :: !Bool,
    -- | Print out which instances of some axioms were used.
    cfg_show_uses_of_axioms :: [String] }

-- | The default configuration.
defaultConfig :: Config
defaultConfig =
  Config {
    cfg_all_lemmas = False,
    cfg_no_lemmas = False,
    cfg_show_instances = False,
    cfg_show_uses_of_axioms = [] }

-- | A proof, with all axioms and lemmas explicitly listed.
data Presentation f =
  Presentation {
    -- | The used axioms.
    pres_axioms :: [Axiom f],
    -- | The used lemmas.
    pres_lemmas :: [Proof f],
    -- | The goals proved.
    pres_goals  :: [ProvedGoal f] }
  deriving Show

-- Note: only the pg_proof field should be trusted!
-- The remaining fields are for information only.
data ProvedGoal f =
  ProvedGoal {
    pg_number  :: Int,
    pg_name    :: String,
    pg_proof   :: Proof f,

    -- Extra fields for existentially-quantified goals, giving the original goal
    -- and the existential witness. These fields are not verified. If you want
    -- to check them, use checkProvedGoal.
    --
    -- In general, subst pg_witness_hint pg_goal_hint == equation pg_proof.
    -- For non-existential goals, pg_goal_hint == equation pg_proof
    -- and pg_witness_hint is the empty substitution.
    pg_goal_hint    :: Equation f,
    pg_witness_hint :: Subst f }
  deriving Show

-- | Construct a @ProvedGoal@.
provedGoal :: Int -> String -> Proof f -> ProvedGoal f
provedGoal number name proof =
  ProvedGoal {
    pg_number = number,
    pg_name = name,
    pg_proof = proof,
    pg_goal_hint = equation proof,
    pg_witness_hint = emptySubst }

-- | Check that pg_goal/pg_witness match up with pg_proof.
checkProvedGoal :: Function f => ProvedGoal f -> ProvedGoal f
checkProvedGoal pg@ProvedGoal{..}
  | subst pg_witness_hint pg_goal_hint == equation pg_proof =
    pg
  | otherwise =
    error $ show $
      text "Invalid ProvedGoal!" $$
      text "Claims to prove" <+> pPrint pg_goal_hint $$
      text "with witness" <+> pPrint pg_witness_hint <#> text "," $$
      text "but actually proves" <+> pPrint (equation pg_proof)

instance Function f => Pretty (Presentation f) where
  pPrint = pPrintPresentation defaultConfig

-- | Simplify and present a proof.
present :: Function f => Config -> [ProvedGoal f] -> Presentation f
present config goals =
  -- First find all the used lemmas, then hand off to presentWithGoals
  presentWithGoals config goals
    (snd (used Set.empty (concatMap (usedLemmas . derivation . pg_proof) goals)))
  where
    used lems [] = (lems, [])
    used lems (x:xs)
      | x `Set.member` lems = used lems xs
      | otherwise =
        let (lems1, ys) = used (Set.insert x lems) (usedLemmas (derivation x))
            (lems2, zs) = used lems1 xs
        in (lems2, ys ++ [x] ++ zs)

presentWithGoals ::
  Function f =>
  Config -> [ProvedGoal f] -> [Proof f] -> Presentation f
presentWithGoals config@Config{..} goals lemmas
  -- We inline a lemma if one of the following holds:
  --   * It only has one step
  --   * It is subsumed by an earlier lemma
  --   * It is only used once
  --   * It has to do with $equals (for printing of the goal proof)
  --   * The option cfg_no_lemmas is true
  -- First we compute all inlinings, then apply simplify to remove them,
  -- then repeat if any lemma was inlined
  | Map.null inlinings =
    let
      axioms = usort $
        concatMap (usedAxioms . derivation . pg_proof) goals ++
        concatMap (usedAxioms . derivation) lemmas
    in
      Presentation axioms
        (map flattenProof lemmas)
        [ decodeGoal (goal { pg_proof = flattenProof pg_proof })
        | goal@ProvedGoal{..} <- goals ]

  | otherwise =
    let
      inline lemma = Map.lookup lemma inlinings

      goals' =
        [ decodeGoal (goal { pg_proof = certify $ simplify inline (derivation pg_proof) })
        | goal@ProvedGoal{..} <- goals ]
      lemmas' =
        [ certify $ simplify inline (derivation lemma)
        | lemma <- lemmas, not (lemma `Map.member` inlinings) ]
    in
      presentWithGoals config goals' lemmas'

  where
    inlinings =
      Map.fromList
        [ (lemma, p)
        | lemma <- lemmas, Just p <- [tryInline lemma]]

    tryInline p
      | shouldInline p = Just (derivation p)
    tryInline p
      -- Check for subsumption by an earlier lemma
      | Just (m, q) <- Map.lookup (canonicalise (t :=: u)) equations, m < n =
        Just (subsume p (derivation q))
      | Just (m, q) <- Map.lookup (canonicalise (u :=: t)) equations, m < n =
        Just (subsume p (Symm (derivation q)))
      where
        t :=: u = equation p
        Just (n, _) = Map.lookup (canonicalise (equation p)) equations
    tryInline _ = Nothing

    shouldInline p =
      cfg_no_lemmas ||
      oneStep (derivation p) ||
      (not cfg_all_lemmas &&
       (isJust (decodeEquality (eqn_lhs (equation p))) ||
        isJust (decodeEquality (eqn_rhs (equation p))) ||
        Map.lookup p uses == Just 1))
  
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
        [ (canonicalise (equation p), (i, p))
        | (i, p) <- zip [0..] lemmas]

    -- Count how many times each lemma is used
    uses =
      Map.fromListWith (+)
        [ (p, 1)
        | p <-
            concatMap usedLemmas
              (map (derivation . pg_proof) goals ++
               map derivation lemmas) ]

    -- Check if a proof only has one step.
    -- Trans only occurs at the top level by this point.
    oneStep Trans{} = False
    oneStep _ = True

invisible :: Function f => Equation f -> Bool
invisible (t :=: u) = show (pPrint t) == show (pPrint u)

-- Pretty-print the proof of a single lemma.
pPrintLemma :: Function f => Config -> (Axiom f -> String) -> (Proof f -> String) -> Proof f -> Doc
pPrintLemma Config{..} axiomNum lemmaNum p =
  ppTerm (eqn_lhs (equation q)) $$ pp (derivation q)
  where
    q = flattenProof p

    pp (Trans p q) = pp p $$ pp q
    pp p | invisible (equation (certify p)) = pPrintEmpty
    pp p =
      (text "= { by" <+>
       ppStep
         (nub (map (show . ppLemma) (usedLemmasAndSubsts p)) ++
          nub (map (show . ppAxiom) (usedAxiomsAndSubsts p))) <+>
       text "}" $$
       ppTerm (eqn_rhs (equation (certify p))))

    ppTerm t = text "  " <#> pPrint t

    ppStep [] = text "reflexivity" -- ??
    ppStep [x] = text x
    ppStep xs =
      hcat (punctuate (text ", ") (map text (init xs))) <+>
      text "and" <+>
      text (last xs)

    ppLemma (p, sub) =
      text "lemma" <+> text (lemmaNum p) <#> showSubst sub
    ppAxiom (axiom@Axiom{..}, sub) =
      text "axiom" <+> text (axiomNum axiom) <+> parens (text axiom_name) <#> showSubst sub

    showSubst sub
      | cfg_show_instances && not (null (substToList sub)) =
        text " with " <#> pPrintSubst sub
      | otherwise = pPrintEmpty

-- Pretty-print a substitution.
pPrintSubst :: Function f => Subst f -> Doc
pPrintSubst sub =
  fsep (punctuate comma
    [ pPrint x <+> text "->" <+> pPrint t
    | (x, t) <- substToList sub ])

-- Transform a proof so that each step uses exactly one axiom
-- or lemma. The proof will have the following form afterwards:
--   * Trans only occurs at the outermost level and is right-associated
--   * Each Cong has exactly one non-Refl argument (no parallel rewriting)
--   * Symm only occurs innermost, i.e., next to UseLemma or UseAxiom
--   * Refl only occurs as an argument to Cong, or outermost if the
--     whole proof is a single reflexivity step
flattenProof :: Function f => Proof f -> Proof f
flattenProof =
  certify . flat . simplify (const Nothing) . derivation
  where
    flat (Trans p q) = trans (flat p) (flat q)
    flat p@(Cong f ps) =
      foldr trans (reflAfter p)
        [ Cong f $
            map reflAfter (take i ps) ++
            [p] ++
            map reflBefore (drop (i+1) ps)
        | (i, q) <- zip [0..] qs,
          p <- steps q ]
      where
        qs = map flat ps
    flat p = p

    reflBefore p = Refl (eqn_lhs (equation (certify p)))
    reflAfter p  = Refl (eqn_rhs (equation (certify p)))

    steps Refl{} = []
    steps (Trans p q) = steps p ++ steps q
    steps p = [p]

    trans (Trans p q) r = trans p (trans q r)
    trans Refl{} p = p
    trans p Refl{} = p
    trans p q =
      case strip q of
        Nothing -> Trans p q
        Just q' -> trans p q'

    strip p
      | t == u = Just (Refl t)
      | otherwise = strip' t p
      where
        t :=: u = equation (certify p)
    strip' t (Trans _ q)
      | eqn_lhs (equation (certify q)) == t = Just q
      | otherwise = strip' t q
    strip' _ _ = Nothing

-- Transform a derivation into a list of single steps.
-- Each step has the following form:
--   * Trans does not occur
--   * Symm only occurs innermost, i.e., next to UseLemma or UseAxiom
--   * Each Cong has exactly one non-Refl argument (no parallel rewriting)
--   * Refl only occurs as an argument to Cong
derivSteps :: Function f => Derivation f -> [Derivation f]
derivSteps = steps . derivation . flattenProof . certify
  where
    steps Refl{} = []
    steps (Trans p q) = steps p ++ steps q
    steps p = [p]

-- | Print a presented proof.
pPrintPresentation :: forall f. Function f => Config -> Presentation f -> Doc
pPrintPresentation config (Presentation axioms lemmas goals) =
  vcat $ intersperse (text "") $
    vcat [ describeEquation "Axiom" (axiomNum axiom) (Just name) eqn $$
           ppAxiomUses axiom
         | axiom@(Axiom _ name eqn) <- axioms,
           not (invisible eqn) ]:
    [ pp "Lemma" (lemmaNum p) Nothing (equation p) emptySubst p
    | p <- lemmas,
      not (invisible (equation p)) ] ++
    [ pp "Goal" (show num) (Just pg_name) pg_goal_hint pg_witness_hint pg_proof
    | (num, ProvedGoal{..}) <- zip [1..] goals ]
  where
    pp kind n mname eqn witness p =
      describeEquation kind n mname eqn $$
      ppWitness witness $$
      text "Proof:" $$
      pPrintLemma config axiomNum lemmaNum p

    axiomNums = Map.fromList (zip axioms [1..])
    lemmaNums = Map.fromList (zip lemmas [length axioms+1..])
    axiomNum x = show (fromJust (Map.lookup x axiomNums))
    lemmaNum x = show (fromJust (Map.lookup x lemmaNums))

    ppWitness sub
      | sub == emptySubst = pPrintEmpty
      | otherwise =
          vcat [
            text "The goal is true when:",
            nest 2 $ vcat
              [ pPrint x <+> text "=" <+> pPrint t
              | (x, t) <- substToList sub ],
            if minimal `elem` funs sub then
              text "where" <+> doubleQuotes (pPrint (minimal :: Fun f)) <+>
              text "stands for an arbitrary term of your choice."
            else pPrintEmpty,
            text ""]

    ppAxiomUses axiom
      | axiom_name axiom `elem` cfg_show_uses_of_axioms config && not (null uses) =
        text "Used with:" $$
        nest 2 (vcat
          [ pPrint i <#> text "." <+> pPrintSubst sub
          | (i, sub) <- zip [1 :: Int ..] uses ])
      | otherwise = pPrintEmpty
      where
        uses = Set.toList (axiomUses axiom)

    axiomUses axiom = Map.findWithDefault Set.empty axiom usesMap
    usesMap =
      Map.fromListWith Set.union
        [ (axiom, Set.singleton (erase (vars sub) sub))
        | goal <- goals,
          let p = derivation (pg_proof goal),
          (axiom, sub) <- groundAxiomsAndSubsts p,
          sub /= emptySubst ]

-- | Format an equation nicely.
--
-- Used both here and in the main file.
describeEquation ::
  PrettyTerm f =>
  String -> String -> Maybe String -> Equation f -> Doc
describeEquation kind num mname eqn =
  text kind <+> text num <#>
  (case mname of
     Nothing -> text ""
     Just name -> text (" (" ++ name ++ ")")) <#>
  text ":" <+> pPrint eqn <#> text "."

----------------------------------------------------------------------
-- Making proofs of existential goals more readable.
----------------------------------------------------------------------

-- The idea: the only axioms which mention $equals, $true and $false
-- are:
--   * $equals(x,x) = $true  (reflexivity)
--   * $equals(t,u) = $false (conjecture)
-- This implies that a proof $true = $false must have the following
-- structure, if we expand out all lemmas:
--   $true = $equals(s,s) = ... = $equals(t,u) = $false.
--
-- The substitution in the last step $equals(t,u) = $false is in fact the
-- witness to the existential.
--
-- Furthermore, we can make it so that the inner "..." doesn't use the $equals
-- axioms. If it does, one of the "..." steps results in either $true or $false,
-- and we can chop off everything before the $true or after the $false.
--
-- Once we have done that, every proof step in the "..." must be a congruence
-- step of the shape
--   $equals(t, u) = $equals(v, w).
-- This is because there are no other axioms which mention $equals. Hence we can
-- split the proof of $equals(s,s) = $equals(t,u) into separate proofs of s=t
-- and s=u.
--
-- What we have got out is:
--   * the witness to the existential
--   * a proof that both sides of the conjecture are equal
-- and we can present that to the user.

-- Decode $equals(t,u) into an equation t=u.
decodeEquality :: Function f => Term f -> Maybe (Equation f)
decodeEquality (App equals (Cons t (Cons u Empty)))
  | isEquals equals = Just (t :=: u)
decodeEquality _ = Nothing

-- Tries to transform a proof of $true = $false into a proof of
-- the original existentially-quantified formula.
decodeGoal :: Function f => ProvedGoal f -> ProvedGoal f
decodeGoal pg =
  case maybeDecodeGoal pg of
    Nothing -> pg
    Just (name, witness, goal, deriv) ->
      checkProvedGoal $
      pg {
        pg_name = name,
        pg_proof = certify deriv,
        pg_goal_hint = goal,
        pg_witness_hint = witness }

maybeDecodeGoal :: forall f. Function f =>
  ProvedGoal f -> Maybe (String, Subst f, Equation f, Derivation f)
maybeDecodeGoal ProvedGoal{..}
  --  N.B. presentWithGoals takes care of expanding any lemma which mentions
  --  $equals, and flattening the proof.
  | isFalseTerm u = extract (derivSteps deriv)
    -- Orient the equation so that $false is the RHS.
  | isFalseTerm t = extract (derivSteps (symm deriv))
  | otherwise = Nothing
  where
    isFalseTerm, isTrueTerm :: Term f -> Bool
    isFalseTerm (App false _) = isFalse false
    isFalseTerm _ = False
    isTrueTerm (App true _) = isTrue true
    isTrueTerm _ = False

    t :=: u = equation pg_proof
    deriv = derivation pg_proof

    -- Detect $true = $equals(t, t).
    decodeReflexivity :: Derivation f -> Maybe (Term f)
    decodeReflexivity (Symm (UseAxiom Axiom{..} sub)) = do
      guard (isTrueTerm (eqn_rhs axiom_eqn))
      (t :=: u) <- decodeEquality (eqn_lhs axiom_eqn)
      guard (t == u)
      return (subst sub t)
    decodeReflexivity _ = Nothing

    -- Detect $equals(t, u) = $false.
    decodeConjecture :: Derivation f -> Maybe (String, Equation f, Subst f)
    decodeConjecture (UseAxiom Axiom{..} sub) = do
      guard (isFalseTerm (eqn_rhs axiom_eqn))
      eqn <- decodeEquality (eqn_lhs axiom_eqn)
      return (axiom_name, eqn, sub)
    decodeConjecture _ = Nothing

    extract (p:ps) = do
      -- Start by finding $true = $equals(t,u).
      t <- decodeReflexivity p
      cont (Refl t) (Refl t) ps
    extract [] = Nothing

    cont p1 p2 (p:ps)
      | Just t <- decodeReflexivity p =
        cont (Refl t) (Refl t) ps
      | Just (name, eqn, sub) <- decodeConjecture p =
        -- If p1: s=t and p2: s=u
        -- then symm p1 `trans` p2: t=u.
        return (name, sub, eqn, symm p1 `trans` p2)
      | Cong eq [p1', p2'] <- p, isEquals eq =
        cont (p1 `trans` p1') (p2 `trans` p2') ps
    cont _ _ _ = Nothing
