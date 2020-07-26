-- | Equational proofs which are checked for correctedness.
{-# LANGUAGE TypeFamilies, PatternGuards, RecordWildCards, ScopedTypeVariables #-}
module Twee.Proof(
  -- * Constructing proofs
  Proof, Derivation(..), Axiom(..),
  certify, equation, derivation,
  -- ** Smart constructors for derivations
  lemma, autoSubst, simpleLemma, axiom, symm, trans, cong, congPath,

  -- * Analysing proofs
  simplify, steps, usedLemmas, usedAxioms, usedLemmasAndSubsts, usedAxiomsAndSubsts,
  groundAxiomsAndSubsts, eliminateDefinitions, eliminateDefinitionsFromGoal,

  -- * Pretty-printing proofs
  Config(..), defaultConfig, Presentation(..),
  ProvedGoal(..), provedGoal, checkProvedGoal,
  pPrintPresentation, present, describeEquation) where

import Twee.Base hiding (invisible)
import Twee.Equation
import Twee.Utils
import qualified Twee.Index as Index
import Control.Monad
import Data.Maybe
import Data.List
import Data.Ord
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.IntMap.Strict as IntMap
import Control.Monad.Trans.State.Strict
import Data.Graph

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
{-# SCC certify #-}
certify :: PrettyTerm f => Derivation f -> Proof f
certify p =
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
    text "subst" <#> pPrintTuple [text "lemma" <+> pPrint (equation lemma), pPrint sub]
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

foldLemmas :: PrettyTerm f => (Map (Proof f) a -> Derivation f -> a) -> [Derivation f] -> Map (Proof f) a
foldLemmas op ds =
  execState (mapM_ foldGoal ds) Map.empty
  where
    foldGoal p = mapM_ foldLemma (usedLemmas p)
    foldLemma p = do
      m <- get
      case Map.lookup p m of
        Just x -> return x
        Nothing -> do
          mapM_ foldLemma (usedLemmas (derivation p))
          m <- get
          case Map.lookup p m of
            Just x  -> return x
            Nothing -> do
              let x = op m (derivation p)
              put (Map.insert p x m)
              return x

mapLemmas :: Function f => (Derivation f -> Derivation f) -> [Derivation f] -> [Derivation f]
mapLemmas f ds = map (derivation . op lem) ds
  where
    op lem = certify . f . unfoldLemmasOnce (\pf -> Just (simpleLemma (lem Map.! pf)))
    lem = foldLemmas op ds

allLemmas :: PrettyTerm f => [Derivation f] -> [Proof f]
allLemmas ds =
  reverse [p | (_, p, _) <- map vertex (topSort graph)]
  where
    used = foldLemmas (\_ p -> usedLemmas p) ds
    (graph, vertex, _) =
      graphFromEdges
        [((), p, ps) | (p, ps) <- Map.toList used]

unfoldLemmasOnce :: Minimal f => (Proof f -> Maybe (Derivation f)) -> Derivation f -> Derivation f
unfoldLemmasOnce lem p@(UseLemma q sub) =
  case lem q of
    Nothing -> p
    Just r ->
      -- Get rid of any variables that are not bound by sub
      -- (e.g., ones which only occur internally in q)
      subst sub (eraseExcept (substDomain sub) r)
unfoldLemmasOnce lem (Symm p) = symm (unfoldLemmasOnce lem p)
unfoldLemmasOnce lem (Trans p q) = trans (unfoldLemmasOnce lem p) (unfoldLemmasOnce lem q)
unfoldLemmasOnce lem (Cong f ps) = cong f (map (unfoldLemmasOnce lem) ps)
unfoldLemmasOnce lem p = p

unfoldLemmas :: Minimal f => (Proof f -> Maybe (Derivation f)) -> Derivation f -> Derivation f
unfoldLemmas lem = unfoldLemmasOnce (\p -> unfoldLemmas lem <$> lem p)

lemma :: Proof f -> Subst f -> Derivation f
lemma p sub = UseLemma p sub

simpleLemma :: PrettyTerm f => Proof f -> Derivation f
simpleLemma p =
  UseLemma p (autoSubst (equation p))

axiom :: Axiom f -> Derivation f
axiom ax@Axiom{..} =
  UseAxiom ax (autoSubst axiom_eqn)

autoSubst :: Equation f -> Subst f
autoSubst eqn =
  fromJust $
  listToSubst [(x, build (var x)) | x <- vars eqn]

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

-- Transform a proof so that each step uses exactly one axiom
-- or lemma. The proof will have the following form afterwards:
--   * Trans only occurs at the outermost level and is right-associated
--   * Each Cong has exactly one non-Refl argument (no parallel rewriting)
--   * Symm only occurs innermost, i.e., next to UseLemma or UseAxiom
--   * Refl only occurs as an argument to Cong, or outermost if the
--     whole proof is a single reflexivity step
flattenProof :: Function f => Proof f -> Proof f
flattenProof = certify . flattenDerivation . derivation

flattenDerivation :: Function f => Derivation f -> Derivation f
flattenDerivation p =
  case steps p of
    [] -> Refl (eqn_lhs (equation (certify p)))
    ps -> foldr1 Trans ps

-- | Simplify a derivation so that:
--   * Symm occurs innermost
--   * Trans is right-associated
--   * Each Cong has at least one non-Refl argument
--   * Refl is not used unnecessarily
simplify :: PrettyTerm f => Derivation f -> Derivation f
simplify (Symm p) = symm (simplify p)
simplify (Trans p q) = trans (simplify p) (simplify q)
simplify (Cong f ps) = cong f (map simplify ps)
simplify p
  | t == u = Refl t
  | otherwise = p
  where
    t :=: u = equation (certify p)

-- | Transform a derivation into a list of single steps.
--   Each step has the following form:
--     * Trans does not occur
--     * Symm only occurs innermost, i.e., next to UseLemma or UseAxiom
--     * Each Cong has exactly one non-Refl argument (no parallel rewriting)
--     * Refl only occurs as an argument to Cong
steps :: Function f => Derivation f -> [Derivation f]
steps = steps1 . simplify
  where
    steps1 p@UseAxiom{} = [p]
    steps1 p@UseLemma{} = [p]
    steps1 (Refl _) = []
    steps1 (Symm p) = map symm (reverse (steps1 p))
    steps1 (Trans p q) = steps1 p ++ steps1 q
    steps1 p@(Cong f qs) =
      concat [ map (inside i) (steps1 q) | (i, q) <- zip [0..] qs ]
      where
        App _ ts :=: App _ us = equation (certify p)
        inside i p =
          Cong f $
            map Refl (take i (unpack us)) ++
            [p] ++
            map Refl (drop (i+1) (unpack ts))

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

-- | Find all ground instances of axioms which are used in the
-- expanded form of a derivation (no lemmas).
groundAxiomsAndSubsts :: Function f => Derivation f -> Map (Axiom f) (Set (Subst f))
groundAxiomsAndSubsts p = ax lem p
  where
    lem = foldLemmas ax [p]

    ax lem (UseAxiom axiom sub) =
      Map.singleton axiom (Set.singleton sub)
    ax lem (UseLemma lemma sub) =
      Map.map (Set.map substAndErase) (lem Map.! lemma)
      where
        substAndErase sub' =
          eraseExcept (vars sub) (subst sub sub')
    ax lem (Symm p) = ax lem p
    ax lem (Trans p q) = Map.unionWith Set.union (ax lem p) (ax lem q)
    ax lem (Cong _ ps) = Map.unionsWith Set.union (map (ax lem) ps)
    ax _ _ = Map.empty

eliminateDefinitionsFromGoal :: Function f => [Axiom f] -> ProvedGoal f -> ProvedGoal f
eliminateDefinitionsFromGoal axioms pg =
  pg {
    pg_proof = certify (eliminateDefinitions axioms (derivation (pg_proof pg))) }

eliminateDefinitions :: Function f => [Axiom f] -> Derivation f -> Derivation f
eliminateDefinitions [] p = p
eliminateDefinitions axioms p = head (mapLemmas elim [p])
  where
    elim (UseAxiom axiom sub)
      | axiom `Set.member` axSet =
        Refl (term (subst sub (eqn_rhs (axiom_eqn axiom))))
      | otherwise = UseAxiom axiom (elimSubst sub)
    elim (UseLemma lemma sub) =
      UseLemma lemma (elimSubst sub)
    elim (Refl t) = Refl (term t)
    elim (Symm p) = Symm (elim p)
    elim (Trans p q) = Trans (elim p) (elim q)
    elim (Cong f ps) =
      case find (build (app f (map var vs))) of
        Nothing -> Cong f (map elim ps)
        Just (rhs, Subst sub) ->
          let proof (Cons (Var (V x)) Empty) = qs !! x in
          replace (proof <$> sub) rhs
      where
        vs = map V [0..length ps-1]
        qs = map (elim . simpleLemma . certify) ps -- avoid duplicating proofs of ts

    elimSubst (Subst sub) = Subst (singleton <$> term <$> unsingleton <$> sub)
      where
        unsingleton (Cons t Empty) = t

    term = build . term'
    term' (Var x) = var x
    term' t@(App f ts) =
      case find t of
        Nothing -> app f (map term' (unpack ts))
        Just (rhs, sub) ->
          term' (subst sub rhs)

    find t =
      listToMaybe $ do
        Axiom{axiom_eqn = l :=: r} <- Index.approxMatches t idx
        sub <- maybeToList (match l t)
        return (r, sub)

    replace sub (Var (V x)) =
      IntMap.findWithDefault undefined x sub
    replace sub (App f ts) =
      cong f (map (replace sub) (unpack ts))

    axSet = Set.fromList axioms
    idx = Index.fromListWith (eqn_lhs . axiom_eqn) axioms

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
data Config f =
  Config {
    -- | Never inline lemmas.
    cfg_all_lemmas :: !Bool,
    -- | Inline all lemmas.
    cfg_no_lemmas :: !Bool,
    -- | Make the proof ground.
    cfg_ground_proof :: !Bool,
    -- | Print out explicit substitutions.
    cfg_show_instances :: !Bool,
    -- | Print out which instances of some axioms were used.
    cfg_show_uses_of_axioms :: Axiom f -> Bool }

-- | The default configuration.
defaultConfig :: Config f
defaultConfig =
  Config {
    cfg_all_lemmas = False,
    cfg_no_lemmas = False,
    cfg_ground_proof = False,
    cfg_show_instances = False,
    cfg_show_uses_of_axioms = const False }

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
present :: Function f => Config f -> [ProvedGoal f] -> Presentation f
present config@Config{..} goals =
  presentRaw [ goal{pg_proof = certify p}
             | (goal, p) <- zip goals ps ]
  where
    maybeGround = if cfg_ground_proof then groundProof else id
    ps = simplifyProofs config $ maybeGround $ map (derivation . pg_proof) goals

presentRaw :: Function f => [ProvedGoal f] -> Presentation f
presentRaw goals =
  Presentation axioms
    (map flattenProof lemmas)
    [ decodeGoal (goal { pg_proof = flattenProof pg_proof })
    | goal@ProvedGoal{..} <- goals ]
  where
    axioms = usort $
      concatMap (usedAxioms . derivation . pg_proof) goals ++
      concatMap (usedAxioms . derivation) lemmas

    lemmas = allLemmas (map (derivation . pg_proof) goals)

groundProof :: Function f => [Derivation f] -> [Derivation f]
groundProof ds
  | all (isGround . equation) (allLemmas ds) = ds
  | otherwise = groundProof (mapLemmas f ds)
  where
    f (UseLemma lemma sub) =
      simpleLemma $ certify $
      eraseExcept (vars sub) $
      subst sub $
      derivation lemma
    f p@UseAxiom{} = p
    f p@Refl{} = p
    f (Symm p) = Symm (f p)
    f (Trans p q) = Trans (f p) (f q)
    f (Cong fun ps) = Cong fun (map f ps)

simplifyProofs :: Function f => Config f -> [Derivation f] -> [Derivation f]
simplifyProofs Config{..} goals = canonical
  where
    -- We inline a lemma if one of the following holds:
    --   * It only has one step
    --   * It is subsumed by an earlier lemma
    --   * It has to do with $equals (for printing of the goal proof)
    --   * The option cfg_no_lemmas is true
    --   * It is only used once
    -- A tricky situation is where:
    --   * Lemma p is used many times, but is just a trivial use of lemma q
    --   * Lemma q is only used by lemma p
    -- In this case we can inline one of p and q, but not both.
    -- To handle this situation correctly, we only compute use counts after
    -- doing all other inlinings.

    triv = pass inlineTrivial goals
    uses = Map.unionsWith (+) $
      map countUses triv ++ Map.elems (foldLemmas (const countUses) triv)
    inlined = pass inlineOnce triv
    canonical = pass canonicaliseLemma inlined

    pass f p = map (op (const derivation) lem) p
      where
        lem = foldLemmas (op f) p
        op f lem p =
          f lem (certify (unfoldLemmasOnce (\lemma -> Just (lem Map.! lemma)) p))

    -- Present the equation left-to-right, and with variables
    -- named canonically
    canonicaliseLemma _ p
      | u `lessEqSkolem` t = canon (derivation p)
      | otherwise = symm (canon (symm (derivation p)))
      where
        t :=: u = equation p
        t' :=: u' = canonicalise (t :=: u)
        Just sub1 = matchEquation (t :=: u) (t' :=: u')
        Just sub2 = matchEquation (t' :=: u') (t :=: u)
        canon p = subst sub2 (simpleLemma (certify (subst sub1 p)))

    inlineTrivial lem p
      | shouldInline p = derivation p
      | (q:_) <- subsuming lem (equation p) = q
      | otherwise = simpleLemma p

    shouldInline p =
      cfg_no_lemmas ||
      length (steps (derivation p)) <= 1 ||
      (not cfg_all_lemmas &&
       (isJust (decodeEquality (eqn_lhs (equation p))) ||
        isJust (decodeEquality (eqn_rhs (equation p)))))

    subsuming lem (t :=: u) =
      subsuming1 lem (t :=: u) ++
      map symm (subsuming1 lem (u :=: t))
    subsuming1 lem eq =
      [ subst sub d
      | (q, d) <- Map.toList lem,
        sub <- maybeToList (matchEquation (equation q) eq) ]

    countUses p =
      Map.fromListWith (+) (zip (usedLemmas p) (repeat (1 :: Int)))

    inlineOnce _ p
      | usedOnce p = derivation p
      | otherwise = simpleLemma p
      where
        usedOnce p =
          case Map.lookup p uses of
            Just 1 | not cfg_all_lemmas -> True
            _ -> False

invisible :: Function f => Equation f -> Bool
invisible (t :=: u) = show (pPrint t) == show (pPrint u)

-- Pretty-print the proof of a single lemma.
pPrintLemma :: Function f => Config f -> (Axiom f -> String) -> (Proof f -> String) -> Proof f -> Doc
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

-- | Print a presented proof.
pPrintPresentation :: forall f. Function f => Config f -> Presentation f -> Doc
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
      | cfg_show_uses_of_axioms config axiom && not (null uses) =
        text "Used with:" $$
        nest 2 (vcat
          [ pPrint i <#> text "." <+> pPrintSubst sub
          | (i, sub) <- zip [1 :: Int ..] uses ])
      | otherwise = pPrintEmpty
      where
        uses = Set.toList (axiomUses axiom)

    axiomUses axiom = Map.findWithDefault Set.empty axiom usesMap
    usesMap =
      Map.unionsWith Set.union
        [ Map.map (Set.delete emptySubst . Set.map ground)
            (groundAxiomsAndSubsts p)
        | goal <- goals,
          let p = derivation (pg_proof goal) ]

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
  | isFalseTerm u = extract (steps deriv)
    -- Orient the equation so that $false is the RHS.
  | isFalseTerm t = extract (steps (symm deriv))
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
