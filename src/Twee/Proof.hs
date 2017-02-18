{-# LANGUAGE TypeFamilies #-}
module Twee.Proof(
  Proof, equation, derivation, Derivation(..), Lemma(..),
  certify, lemmaEquation, 
  simplify, step, symm, trans, cong) where

import Twee.Base
import Twee.Equation
import Control.Monad
import Data.Maybe

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

instance Pretty (Proof f) where pPrint _ = text "<proof>"
instance Pretty (Derivation f) where pPrint = pPrint . certify

-- Simplify a derivation.
simplify p@Step{} = p
simplify p@Refl{} = p
simplify (Symm p) = symm (simplify p)
simplify (Trans p q) = trans (simplify p) (simplify q)
simplify (Cong f ps) = cong f (map simplify ps)

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

-- -- Pretty-print the proof of a single lemma.
-- pPrintProof :: PrettyTerm f =>
--   -- For opportunistically replacing rules.
--   (VersionedId -> (Either String VersionedId, Direction)) ->
--   Proof f -> Doc
-- pPrintProof replace (Proof ps) =
--   pp (concatMap simplify ps)
--   where
--     simplify :: ProofStep f -> [ProofStep f]
--     simplify (ProofStep dir p) = ProofStep dir <$> simplifyDir p
--     simplifyDir (Reduction p) = Reduction <$> flatten p
--     simplifyDir p@Axiom{} = [p]

--     -- Transform each reduction so it only uses Step, Cong and Refl,
--     -- and no top-level Refls.
--     flatten Refl{} = []
--     flatten (Trans p q) = flatten p ++ flatten q
--     flatten (Cong f ps) = map (cong f) (transpose (flattenPad ps))
--     flatten p@Step{} = [p]

--     -- Given a list of (unrelated) reductions, flatten each of them,
--     -- making each flattened reduction have the same length
--     -- (by padding with Refl)..
--     flattenPad ps =
--       map (take (maximum (0:map length pss))) $
--       zipWith pad ps pss
--       where
--         pad p ps = ps ++ repeat (Refl (result p))
--         pss = map flatten ps

--     pp [] = text "reflexivity"
--     pp ps@(p0:_) =
--       vcat $
--         ppTerm (stepInitial p0):
--         [ text "= { by" <+> ppStep p <+> text "}" $$
--           ppTerm (stepResult p)
--         | p <- ps ]

--     ppTerm t = text "  " <> pPrint t

--     ppStep (ProofStep dir p) =
--       hcat (punctuate "; " (map ppGroup groups))
--       where
--         used = [ (x, dir `mappend` dir') | (x, dir') <- usort (findSteps p) ]
--         groups = partitionBy (\(x, dir) -> (isRight x, dir)) used

--     ppGroup group@((rule, dir):_) =
--       text (if isLeft rule then "axiom" else "rule") <>
--       text (if length group > 1 then "s" else "") <+>
--       hcat (punctuate (text ", ") (map ppLaw (init group))) <+>
--       ppLaw (last group) <>
--       case dir of
--         Forwards -> text ""
--         Backwards -> text " backwards"
--       where
--         ppLaw (Left name, _) = text name
--         ppLaw (Right n, _) = pPrint n

--     findSteps (Axiom name _ _) = [(Left name, Forwards)]
--     findSteps (Reduction p) = [replace n | (n, _, _) <- steps p]

-- -- Pretty-print a complete proof.
-- pPrintTheorem ::
--   forall f a. (PrettyTerm f, Has a (Proof f), Has a (Rule f)) =>
--   Map VersionedId a ->
--   [(String, Equation f, Proof f)] ->
--   String
-- pPrintTheorem rules goals =
--   unlines $ intercalate [""] $
--     [ pp ("Lemma " ++ prettyShow n) (unorient (the rule)) (the rule)
--     | n <- Set.toList usedRules,
--       let rule = fromJust (Map.lookup n rules)] ++
--     [ pp ("Goal " ++ name) eqn proof
--     | (name, eqn, proof) <- goals ]
--   where
--     pp title eqn p =
--       let
--         repl n = replace (unorient (the (fromJust (Map.lookup n rules)))) in
--       [ title ++ ": " ++ prettyShow eqn ++ ".",
--         "Proof:" ] ++
--       lines (show (pPrintProof repl p))

--     -- Compute which rules are used in the proof.
--     usedRules :: Set VersionedId
--     usedRules =
--       usedRulesFrom Set.empty
--         (concat [proofRules proof | (_, _, proof) <- goals])

--     usedRulesFrom used [] = used
--     usedRulesFrom used ((n, eqn):xs) =
--       case replace eqn of
--         (Right n, _) ->
--           usedRulesFrom (Set.insert n used)
--           (proofRules (the (fromJust (Map.lookup n rules))) ++ xs)
--         (Left _, _) ->
--           usedRulesFrom used xs

--     proofRules :: Proof f -> [(VersionedId, Equation f)]
--     proofRules (Proof ps) =
--       usort $
--       [ (n, unorient rule)
--       | ProofStep _ (Reduction p) <- ps,
--         (n, rule, _) <- steps p ]

--     -- Replace a rule with an equivalent rule or an axiom.
--     replace :: Equation f -> (Either String VersionedId, Direction)
--     replace eqn =
--       let
--         (n, dir) =
--           fromJust (Map.lookup eqn equations)
--       in
--         case Map.lookup n axioms of
--           Nothing -> (Right n, dir)
--           Just (ax, dir') -> (Left ax, dir `mappend` dir')

--     -- Rules whose proofs are just a single axiom.
--     axioms :: Map VersionedId (String, Direction)
--     axioms =
--       Map.mapMaybe
--         (\rule ->
--            case the rule :: Proof f of
--              Proof [ProofStep dir (Axiom name _ _)] -> Just (name, dir)
--              _ -> Nothing)
--         rules

--     -- For each equation, the earliest rule which proves that equation.
--     equations :: Map (Equation f) (VersionedId, Direction)
--     equations =
--       Map.fromListWith min $ concat
--         [ [(t :=: u, (n, Forwards)), (u :=: t, (n, Backwards))]
--         | (n, rule) <- Map.toList rules,
--           let t = lhs (the rule)
--               u = rhs (the rule) ]
