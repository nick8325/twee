{-# LANGUAGE CPP, RecordWildCards, FlexibleInstances #-}
#include "errors.h"
import Control.Monad
import Data.Char
import Data.Either
import Twee hiding (message)
import Twee.Base hiding (char, lookup, (<>))
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof(Axiom(..), Lemma(..), describeEquation, Presentation(..))
import Twee.Pretty
import Twee.Utils
import qualified Twee.CP as CP
import Data.Ord
import qualified Data.Map.Strict as Map
import qualified Twee.KBO as KBO
import Data.List.Split
import Data.List
import Data.Maybe
import Jukebox.Options
import Jukebox.Toolbox
import Jukebox.Name
import qualified Jukebox.Form as Jukebox
import Jukebox.Form hiding ((:=:), Var, Symbolic(..), Term, Axiom)
import Jukebox.Monotonox.ToFOF
import Jukebox.TPTP.Print

parseConfig :: OptionParser Config
parseConfig =
  Config <$> maxSize <*> maxCPs <*> (CP.Config <$> lweight <*> rweight <*> funweight <*> varweight)
  where
    maxSize =
      inGroup "Resource limits" $
      flag "max-term-size" ["Only generate rewrite rules up to this size (unlimited by default)."] maxBound argNum
    maxCPs =
      inGroup "Resource limits" $
      flag "max-cps" ["Give up after considering this many critical pairs (unlimited by default)."] maxBound argNum
    lweight =
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "lhs-weight" "Weight given to LHS of critical pair" (CP.cfg_lhsweight . cfg_critical_pairs) argNum
    rweight =
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "rhs-weight" "Weight given to RHS of critical pair" (CP.cfg_rhsweight . cfg_critical_pairs) argNum
    funweight =
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "fun-weight" "Weight given to function symbols" (CP.cfg_funweight . cfg_critical_pairs) argNum
    varweight =
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "var-weight" "Weight given to variable symbols" (CP.cfg_varweight . cfg_critical_pairs) argNum
    defaultFlag name desc field parser =
      flag name [desc ++ " (defaults to " ++ show def ++ ")."] def parser
      where
        def = field defaultConfig

parsePrecedence :: OptionParser [String]
parsePrecedence =
  inGroup "Term order options" $
  fmap (splitOn ",")
  (flag "precedence" ["List of functions in descending order of precedence"] [] (arg "<function>" "expected a function name" Just))

parseTSTP :: OptionParser Bool
parseTSTP =
  inGroup "Output options" $
  bool "tstp"
    ["Print proof in TSTP format."]

data Constant =
  Constant {
    con_prec  :: {-# UNPACK #-} !Precedence,
    con_id    :: {-# UNPACK #-} !Jukebox.Function,
    con_arity :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord)

data Precedence = Precedence !Bool !(Maybe Int) !Int
  deriving (Eq, Ord)

instance Sized Constant where
  size con@Constant{..} = if con_arity >= 2 then 0 else 1
instance Arity Constant where
  arity Constant{..} = con_arity

instance Pretty Constant where
  pPrint Constant{..} = text (base con_id)

instance PrettyTerm Constant where
  termStyle Constant{..}
    | any isAlphaNum (base con_id) = uncurried
    | otherwise =
      case con_arity of
        1 -> prefix
        2 -> infixStyle 5
        _ -> uncurried

instance Ordered (Extended Constant) where
  f << g = fun_value f < fun_value g
  lessEq t u = {-# SCC lessEq #-} KBO.lessEq t u
  lessIn model t u = {-# SCC lessIn #-} KBO.lessIn model t u

data TweeContext =
  TweeContext {
    ctx_var     :: Jukebox.Variable,
    ctx_minimal :: Jukebox.Function,
    ctx_true    :: Jukebox.Function,
    ctx_false   :: Jukebox.Function,
    ctx_equals  :: Jukebox.Function,
    ctx_type    :: Type }

-- Convert back and forth between Twee and Jukebox.
tweeConstant :: Precedence -> Jukebox.Function -> Constant
tweeConstant prec fun =
  Constant prec fun (Jukebox.arity fun)

jukeboxFunction :: TweeContext -> Extended Constant -> Jukebox.Function
jukeboxFunction _ (Function Constant{..}) = con_id
jukeboxFunction TweeContext{..} EqualsCon = ctx_equals
jukeboxFunction TweeContext{..} TrueCon = ctx_true
jukeboxFunction TweeContext{..} FalseCon = ctx_false
jukeboxFunction TweeContext{..} Minimal = ctx_minimal
jukeboxFunction TweeContext{..} (Skolem _) =
  error "Skolem variable leaked into rule"

tweeTerm :: (Jukebox.Function -> Precedence) -> Jukebox.Term -> Term (Extended Constant)
tweeTerm prec t = build (tm t)
  where
    tm (Jukebox.Var (Unique x _ _ ::: _)) =
      var (V (fromIntegral x))
    tm (f :@: ts) =
      app (fun (Function (tweeConstant (prec f) f))) (map tm ts)

jukeboxTerm :: TweeContext -> Term (Extended Constant) -> Jukebox.Term
jukeboxTerm TweeContext{..} (Var (V x)) =
  Jukebox.Var (Unique (fromIntegral x) "X" defaultRenamer ::: ctx_type)
jukeboxTerm ctx@TweeContext{..} (App f t) =
  jukeboxFunction ctx (fun_value f) :@: map (jukeboxTerm ctx) ts
  where
    ts = unpack t

makeContext :: Problem Clause -> TweeContext
makeContext prob = run prob $ \prob -> do
  let
    ty =
      case types' prob of
        []   -> Type (name "$i") Infinite Infinite
        [ty] -> ty

  var     <- newSymbol "X" ty
  minimal <- newFunction "$constant" [] ty
  equals  <- newFunction "$equals" [ty, ty] ty
  false   <- newFunction "$false_term" [] ty
  true    <- newFunction "$true_term" [] ty

  return TweeContext {
    ctx_var = var,
    ctx_minimal = minimal,
    ctx_equals = equals,
    ctx_false = false,
    ctx_true = true,
    ctx_type = ty }

-- Encode existentials so that all goals are ground.
addNarrowing :: TweeContext -> Problem Clause -> Problem Clause
addNarrowing TweeContext{..} prob =
  unchanged ++ equalityClauses
  where
    (unchanged, nonGroundGoals) = partitionEithers (map f prob)
      where
        f inp@Input{what = Clause (Bind _ [Neg (x Jukebox.:=: y)])} =
          Right (inp, (x, y))
        f inp = Left inp

    equalityClauses
      | null nonGroundGoals = []
      | otherwise =
        -- Turn a != b & c != d & ...
        -- into eq(a,b)=false & eq(c,d)=false & eq(X,X)=true & true!=false (esa)
        -- and then extract the individual components (thm)
        let
          equalityLiterals =
            -- true != false
            ("true_equals_false", Neg ((ctx_true :@:) [] Jukebox.:=: (ctx_false :@: []))):
            -- eq(X,X)=true
            ("reflexivity", Pos (ctx_equals :@: [Jukebox.Var ctx_var, Jukebox.Var ctx_var] Jukebox.:=: (ctx_true :@: []))):
            -- [eq(a,b)=false, eq(c,d)=false, ...]
            [ (tag, Pos (ctx_equals :@: [x, y] Jukebox.:=: (ctx_false :@: [])))
            | (Input{tag = tag}, (x, y)) <- nonGroundGoals ]

          -- Equisatisfiable to the input clauses
          justification =
            Input {
              tag  = "new_negated_conjecture",
              kind = Jukebox.Axiom,
              what = toForm (clause (map snd equalityLiterals)),
              source =
                Inference "encode_existential" "esa"
                  (map (fmap toForm . fst) nonGroundGoals) }

          input tag form =
            Input {
              tag = tag,
              kind = Conjecture,
              what = clause [form],
              source =
                Inference "split_conjunct" "thm" [justification] }

        in [input tag form | (tag, form) <- equalityLiterals]

-- Split the problem into axioms and ground goals.
identifyProblem ::
  TweeContext -> Problem Clause ->
  ([Input (Jukebox.Term, Jukebox.Term)],
   [Input (Jukebox.Term, Jukebox.Term)])
identifyProblem TweeContext{..} prob =
  partitionEithers (map identify prob)

  where
    toInput inp x =
      Input {
        tag = tag inp,
        kind = kind inp,
        what = x,
        source = Inference "tautology" "thm" [fmap toForm inp] }

    identify inp@Input{what = Clause (Bind _ [Pos (t Jukebox.:=: u)])} =
      Left (toInput inp (t, u))
    identify inp@Input{what = Clause (Bind _ [Neg (t Jukebox.:=: u)])}
      | ground t && ground u =
        Right (toInput inp (t, u))
    identify inp@Input{what = Clause (Bind _ [])} =
      -- The empty clause can appear after clausification if
      -- the conjecture was trivial
      Left (toInput inp (Jukebox.Var ctx_var, ctx_minimal :@: []))
    identify inp =
      error ("Problem contains a non-UEQ axiom:\n  " ++ show (prettyNames inp) ++ "\n")

runTwee :: GlobalFlags -> Bool -> Config -> [String] -> Problem Clause -> IO Answer
runTwee globals tstp config precedence obligs = {-# SCC runTwee #-} do
  let
    -- Encode whatever needs encoding in the problem
    ctx = makeContext obligs
    prob = addNarrowing ctx obligs
    (axioms0, goals0) = identifyProblem ctx prob

    -- Work out a precedence for function symbols
    prec c =
      Precedence
        (isNothing (elemIndex (base c) precedence))
        (fmap negate (elemIndex (base c) precedence))
        (negate (funOcc c prob))

    -- Translate everything to Twee.
    toEquation (t, u) =
      canonicalise (tweeTerm prec t :=: tweeTerm prec u)

    goals =
      [ goal n (tag inp) (toEquation (what inp))
      | (n, inp) <- zip [1..] goals0 ]
    axioms =
      [ Axiom n (tag inp) (toEquation (what inp))
      | (n, inp) <- zip [1..] axioms0 ]

    withGoals = foldl' (addGoal config) initialState goals
    withAxioms = foldl' (addAxiom config) withGoals axioms

  let
    line = unless (quiet globals) (putStrLn "")
    say msg =
      unless (quiet globals) $
        if tstp then message globals msg else putStr (unlines (lines msg))
    output = Output {
      output_report = \state -> do
        line
        say (report state)
        line,
      output_message = say . prettyShow }

  line
  say "Here is the input problem:"
  forM_ axioms $ \Axiom{..} ->
    say $ "  " ++
      describeEquation "Axiom"
        (show axiom_number) (Just axiom_name) axiom_eqn
  forM_ goals $ \Goal{..} ->
    say $ "  " ++
      describeEquation "Goal"
        (show goal_number) (Just goal_name) goal_eqn

  line
  state <- complete output config withAxioms
  line

  when (solved state) $ do
    let
      sol = solutions state
      pres =
        Proof.present
          [ (name, proof)
          | (Goal{goal_name = name}, proof) <- solutions state ]

    say ("Proved the following conjecture" ++ if length sol > 1 then "s:" else ":")
    forM_ sol $ \(Goal{..}, _) ->
      say $ "  " ++
        describeEquation "Goal"
          (show goal_number) (Just goal_name) goal_eqn
    say "The proof is as follows."
    line
    say $ prettyShow $ Proof.present
      [ (name, proof)
      | (Goal{goal_name = name}, proof) <- solutions state ]

    when tstp $ do
      say "SZS output start CNFRefutation"
      -- print (pPrintProof ( pres)
      -- XXX transform back to Jukebox and then use Jukebox.pPrintProof
      say "SZS output end CNFRefutation"
      return ()

    line

  return $
    if solved state then Unsatisfiable else NoAnswer GaveUp

-- pPrintTSTPEquation :: PrettyTerm f => Equation f -> Doc
-- pPrintTSTPEquation (t :=: u) =
--   pPrintTSTPTerm t <+> text "=" <+> pPrintTSTPTerm u

-- pPrintTSTPTerm :: PrettyTerm f => Term f -> Doc
-- pPrintTSTPTerm (Var x) = pPrint x
-- pPrintTSTPTerm (App f t) =
--   text (escapeAtom (prettyShow f)) <>
--   case ts of
--     [] -> text ""
--     _ ->
--       parens (hcat (punctuate comma (map pPrintTSTPTerm ts)))
--   where
--     ts = unpack t

-- pPrintTSTP :: PrettyTerm f => Presentation f -> Doc
-- pPrintTSTP Presentation{..} =
--   vcat $
--     [ ppProof (ppLemma lemma) (lemma_proof lemma)
--     | lemma <- pres_lemmas ] ++
--     [ ppProof name (snd goal) $$
--       fun "cnf"
--         [text "contradiction_" <> name,
--          text "plain",
--          text "$false",
--          inference "resolution" "thm"
--            [name, text "negated_" <> name]] <> text "."
--     | (i, goal) <- zip [1..] pres_goals,
--       let name = text "goal" <> pPrint (i :: Int) ]
--   where
--     clause num eqn reason =
--       fun "cnf" [num, text "plain", pPrintTSTPEquation eqn, reason] <>
--       text "."

--     inference name status used =
--       fun "inference"
--         [name,
--          list [text "status" <> parens (text status)],
--          list used]

--     list :: [Doc] -> Doc
--     list = brackets . hcat . punctuate comma

--     fun :: String -> [Doc] -> Doc
--     fun f xs = text f <> parens (hcat (punctuate comma xs))

--     ppLemma Lemma{..} = text "lem" <> pPrint lemma_id
--     ppAxiom Axiom{..} = text "ax" <> pPrint axiom_number

--     ppProof name p =
--       fst $ from Nothing (Proof.derivation p)
--       where
--         makeName Nothing = name
--         makeName (Just n) = name <> text "_" <> pPrint (n :: Int)

--         makeClause mn p used =
--           clause (makeName mn) (Proof.equation (Proof.certify p))
--             (inference "rw" "thm" used)

--         used p =
--           map ppLemma (usortBy (comparing lemma_id) (Proof.usedLemmas p)) ++
--           map ppAxiom (usort (Proof.usedAxioms p))

--         from mn p@(Proof.Trans q r) =
--           let
--             (doc1, used1) = from (Just (fromMaybe 0 mn + 1)) r
--             used2 = used q
--           in
--             (doc1 $$ makeClause mn p (used1 ++ used2), [makeName mn])
--         from mn p =
--           (makeClause mn p (used p), [makeName mn])

main = do
  let twee = Tool "twee" "twee - the Wonderful Equation Engine" "1" "Reads in an equational problem and tries to prove it"
  join . parseCommandLine twee . tool twee $
    greetingBox twee =>>
    allFilesBox <*>
      (parseProblemBox =>>=
       (toFofIO <$> globalFlags <*> clausifyBox <*> pure (tags False)) =>>=
       clausifyBox =>>=
       allObligsBox <*>
         (runTwee <$> globalFlags <*> parseTSTP <*> parseConfig <*> parsePrecedence))
