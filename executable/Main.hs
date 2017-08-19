{-# LANGUAGE CPP, RecordWildCards, FlexibleInstances #-}
#include "errors.h"
import Control.Monad
import Data.Char
import Data.Either
import Twee hiding (message)
import Twee.Base hiding (char, lookup, vars)
import Twee.Rule(lhs, rhs, unorient)
import Twee.Equation
import qualified Twee.Proof as Proof
import Twee.Proof hiding (Config, defaultConfig)
import qualified Twee.Join as Join
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
import Jukebox.Name hiding (lhs, rhs)
import qualified Jukebox.Form as Jukebox
import Jukebox.Form hiding ((:=:), Var, Symbolic(..), Term, Axiom, size)
import Jukebox.Monotonox.ToFOF
import Jukebox.TPTP.Print
import qualified Data.Set as Set
import qualified Data.IntMap.Strict as IntMap
import System.IO
import System.Exit

data MainFlags =
  MainFlags {
    flags_proof :: Bool,
    flags_trace :: Maybe String }

parseMainFlags :: OptionParser MainFlags
parseMainFlags =
  MainFlags <$> proof <*> trace
  where
    proof =
      inGroup "Output options" $
      bool "proof" ["Produce proofs (on by default)."]
      True
    trace =
      expert $
      inGroup "Output options" $
      flag "trace" ["Write a Prolog-format execution trace to this file (off by default)."]
        Nothing (Just <$> argFile)

parseConfig :: OptionParser Config
parseConfig =
  Config <$> maxSize <*> maxCPs <*> maxCPDepth <*> simplify <*> improve <*>
    (CP.Config <$> lweight <*> rweight <*> funweight <*> varweight <*> depthweight) <*>
    (Join.Config <$> ground_join <*> connectedness <*> set_join) <*>
    (Proof.Config <$> all_lemmas <*> flat_proof <*> show_instances)
  where
    maxSize =
      inGroup "Resource limits" $
      flag "max-term-size" ["Discard rewrite rules whose left-hand side is bigger than this limit (unlimited by default)."] maxBound argNum
    maxCPs =
      inGroup "Resource limits" $
      flag "max-cps" ["Give up after considering this many critical pairs (unlimited by default)."] maxBound argNum
    maxCPDepth =
      inGroup "Resource limits" $
      flag "max-cp-depth" ["Only consider critical pairs up to this depth (unlimited by default)."] maxBound argNum
    simplify =
      expert $
      inGroup "Completion heuristics" $
      bool "simplify"
        ["Simplify rewrite rules with respect to one another (on by default)."]
        True
    improve =
      expert $
      inGroup "Search strategy" $
      bool "improve"
        ["Try to improve critical pairs to nicer ones (off by default)."]
        False
    lweight =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "lhs-weight" "Weight given to LHS of critical pair" (CP.cfg_lhsweight . cfg_critical_pairs) argNum
    rweight =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "rhs-weight" "Weight given to RHS of critical pair" (CP.cfg_rhsweight . cfg_critical_pairs) argNum
    funweight =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "fun-weight" "Weight given to function symbols" (CP.cfg_funweight . cfg_critical_pairs) argNum
    varweight =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "var-weight" "Weight given to variable symbols" (CP.cfg_varweight . cfg_critical_pairs) argNum
    depthweight =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "depth-weight" "Weight given to critical pair depth" (CP.cfg_depthweight . cfg_critical_pairs) argNum
    ground_join =
      expert $
      inGroup "Critical pair joining heuristics" $
      not <$>
      bool "ground-joining"
        ["Test terms for ground joinability (on by default)."]
        True
    connectedness =
      expert $
      inGroup "Critical pair joining heuristics" $
      not <$>
      bool "connectedness"
        ["Test terms for subconnectedness (on by default)."]
        True
    set_join =
      expert $
      inGroup "Critical pair joining heuristics" $
      bool "set-join"
        ["Compute all normal forms when joining critical pairs (off by default)."]
        False
    all_lemmas =
      expert $
      inGroup "Proof presentation" $
      bool "all-lemmas"
        ["Produce a proof with one lemma for each critical pair (off by default)."]
        False
    flat_proof =
      expert $
      inGroup "Proof presentation" $
      bool "no-lemmas"
        ["Produce a proof with no lemmas (off by default).",
         "May lead to exponentially large proofs."]
        False
    show_instances =
      expert $
      inGroup "Proof presentation" $
      bool "show-instances"
        ["Show which instances of each axiom and lemma were used (off by default)."]
        False
    defaultFlag name desc field parser =
      flag name [desc ++ " (" ++ show def ++ " by default)."] def parser
      where
        def = field defaultConfig

parsePrecedence :: OptionParser [String]
parsePrecedence =
  expert $
  inGroup "Term order options" $
  fmap (splitOn ",")
  (flag "precedence" ["List of functions in descending order of precedence."] [] (arg "<function>" "expected a function name" Just))

data Constant =
  Constant {
    con_prec  :: {-# UNPACK #-} !Precedence,
    con_id    :: {-# UNPACK #-} !Jukebox.Function,
    con_arity :: {-# UNPACK #-} !Int }
  deriving (Eq, Ord)

data Precedence = Precedence !Bool !(Maybe Int) !Int
  deriving (Eq, Ord)

instance Sized Constant where
  size Constant{..} = 1
    --if con_arity <= 1 then 1 else 0
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
tweeConstant :: TweeContext -> Precedence -> Jukebox.Function -> Extended Constant
tweeConstant TweeContext{..} prec fun
  | fun == ctx_minimal = Minimal
  | fun == ctx_true = TrueCon
  | fun == ctx_false = FalseCon
  | fun == ctx_equals = EqualsCon
  | otherwise = Function (Constant prec fun (Jukebox.arity fun))

jukeboxFunction :: TweeContext -> Extended Constant -> Jukebox.Function
jukeboxFunction _ (Function Constant{..}) = con_id
jukeboxFunction TweeContext{..} EqualsCon = ctx_equals
jukeboxFunction TweeContext{..} TrueCon = ctx_true
jukeboxFunction TweeContext{..} FalseCon = ctx_false
jukeboxFunction TweeContext{..} Minimal = ctx_minimal
jukeboxFunction TweeContext{..} (Skolem _) =
  error "Skolem variable leaked into rule"

tweeTerm :: TweeContext -> (Jukebox.Function -> Precedence) -> Jukebox.Term -> Term (Extended Constant)
tweeTerm ctx prec t = build (tm t)
  where
    tm (Jukebox.Var (Unique x _ _ ::: _)) =
      var (V (fromIntegral x))
    tm (f :@: ts) =
      app (fun (tweeConstant ctx (prec f) f)) (map tm ts)

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
        f inp@Input{what = Clause (Bind _ [Neg (x Jukebox.:=: y)])}
          | not (ground x) || not (ground y) =
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
              kind = Jukebox.Axiom "negated_conjecture",
              what =
                let form = And (map (Literal . snd) equalityLiterals) in
                ForAll (Bind (Set.fromList (vars form)) form),
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

data PreEquation =
  PreEquation {
    pre_name :: String,
    pre_form :: Input Form,
    pre_eqn  :: (Jukebox.Term, Jukebox.Term) }

-- Split the problem into axioms and ground goals.
identifyProblem ::
  TweeContext -> Problem Clause -> Either (Input Clause) ([PreEquation], [PreEquation])
identifyProblem TweeContext{..} prob =
  fmap partitionEithers (mapM identify prob)

  where
    pre inp x =
      PreEquation {
        pre_name = tag inp,
        pre_form = fmap toForm inp,
        pre_eqn = x }

    identify inp@Input{what = Clause (Bind _ [Pos (t Jukebox.:=: u)])} =
      return $ Left (pre inp (t, u))
    identify inp@Input{what = Clause (Bind _ [Neg (t Jukebox.:=: u)])}
      | ground t && ground u =
        return $ Right (pre inp (t, u))
    identify inp@Input{what = Clause (Bind _ [])} =
      -- The empty clause can appear after clausification if
      -- the conjecture was trivial
      return $ Left (pre inp (Jukebox.Var ctx_var, ctx_minimal :@: []))
    identify inp = Left inp

runTwee :: GlobalFlags -> TSTPFlags -> MainFlags -> Config -> [String] -> (IO () -> IO ()) -> Problem Clause -> IO Answer
runTwee globals (TSTPFlags tstp) main config precedence later obligs = {-# SCC runTwee #-} do
  let
    -- Encode whatever needs encoding in the problem
    ctx = makeContext obligs
    prob = addNarrowing ctx obligs

  (axioms0, goals0) <-
    case identifyProblem ctx prob of
      Left inp -> do
        hPutStr stderr $
          unlines $
            ["The problem contains the following clause, which is not a unit equality:"] ++
            ["  " ++ line | line <- lines $ show (pPrintClauses [inp])] ++
            ["Twee only handles unit equality problems."]
        exitWith (ExitFailure 1)
      Right x -> return x

  let
    -- Work out a precedence for function symbols
    prec c =
      Precedence
        (isNothing (elemIndex (base c) precedence))
        (fmap negate (elemIndex (base c) precedence))
        (negate (funOcc c prob))

    -- Translate everything to Twee.
    toEquation (t, u) =
      canonicalise (tweeTerm ctx prec t :=: tweeTerm ctx prec u)

    goals =
      [ goal n pre_name (toEquation pre_eqn)
      | (n, PreEquation{..}) <- zip [1..] goals0 ]
    axioms =
      [ Axiom n pre_name (toEquation pre_eqn)
      | (n, PreEquation{..}) <- zip [1..] axioms0 ]

    withGoals = foldl' (addGoal config) initialState goals
    withAxioms = foldl' (addAxiom config) withGoals axioms

  -- Set up tracing.
  sayTrace <-
    case flags_trace main of
      Nothing -> return $ \_ -> return ()
      Just file -> do
        h <- openFile file WriteMode
        hSetBuffering h LineBuffering
        return $ \msg -> hPutStrLn h msg
  sayTrace ":- style_check(-singleton)."
  
  let
    say msg = unless (quiet globals) (putStrLn msg)
    line = say ""
    output = Output {
      output_report = \state -> do
        line
        say (report state)
        line,
      output_message = \msg -> do
        say (prettyShow msg)
        sayTrace (show (traceMsg msg)) }

    traceMsg (NewActive Active{..}) =
      step "new"
        [pPrint active_id, traceEqn (unorient active_rule)]
    traceMsg (NewEquation eqn) =
      step "hard" [traceEqn eqn]
    traceMsg (DeleteActive Active{..}) =
      step "delete"
        [pPrint active_id, traceEqn (unorient active_rule)]
    traceMsg SimplifyQueue =
      step "simplify_queue" []
    traceMsg Interreduce =
      step "interreduce" []

    traceEqn (t :=: u) =
      pPrintPrec prettyNormal 6 t <+> text "=" <+> pPrintPrec prettyNormal 6 u
    traceApp f xs =
      pPrintTerm uncurried prettyNormal 0 (text f) xs

    step :: String -> [Doc] -> Doc
    step f xs = traceApp "step" [traceApp f xs] <> text "."

  say "Here is the input problem:"
  forM_ axioms $ \Axiom{..} ->
    say $ show $ nest 2 $
      describeEquation "Axiom"
        (show axiom_number) (Just axiom_name) axiom_eqn
  forM_ goals $ \Goal{..} ->
    say $ show $ nest 2 $
      describeEquation "Goal"
        (show goal_number) (Just goal_name) goal_eqn
  line

  state <- complete output config withAxioms
  line

  when (solved state && flags_proof main) $ later $ do
    let
      pres = present (cfg_proof_presentation config) (solutions state)

    sayTrace ""
    forM_ (pres_lemmas pres) $ \Lemma{..} ->
      sayTrace $ show $
        traceApp "lemma" [traceEqn (equation lemma_proof)] <> text "."

    when tstp $ do
      putStrLn "% SZS output start CNFRefutation"
      print $ pPrintProof $
        presentToJukebox ctx
          (zip (map axiom_number axioms) (map pre_form axioms0))
          (zip (map goal_number goals) (map pre_form goals0))
          pres
      putStrLn "% SZS output end CNFRefutation"
      putStrLn ""

    putStrLn "The conjecture is true! Here is a proof."
    putStrLn ""
    print $ pPrintPresentation (cfg_proof_presentation config) pres
    putStrLn ""

  when (not (quiet globals) && not (solved state)) $ later $ do
    let
      state' = interreduce config state
      score rule =
        (size (lhs rule), lhs rule,
         size (rhs rule), rhs rule)
      actives =
        sortBy (comparing (score . active_rule)) $
        IntMap.elems (st_active_ids state')

    putStrLn "Ran out of critical pairs. Here is the final rewrite system:"
    forM_ actives $ \active ->
      putStrLn ("  " ++ prettyShow (canonicalise (active_rule active)))
    putStrLn ""

  return $
    if solved state then Unsat Unsatisfiable else NoAnswer GaveUp

-- Transform a proof presentation into a Jukebox proof.
presentToJukebox ::
  TweeContext ->
  -- Axioms, indexed by axiom number.
  [(Int, Input Form)] ->
  -- N.B. the formula here proves the negated goal.
  [(Int, Input Form)] ->
  Presentation (Extended Constant) ->
  Problem Form
presentToJukebox ctx axioms goals Presentation{..} =
  [ Input {
      tag = pg_name,
      kind = Jukebox.Axiom "axiom",
      what = false,
      source =
        Inference "resolution" "thm"
          [-- A proof of t != u
           fromJust (lookup pg_number goals),
           -- A proof of t = u
           fromJust (Map.lookup pg_number goal_proofs)] }
  | ProvedGoal{..} <- pres_goals ]

  where
    axiom_proofs =
      Map.fromList
        [ (axiom_number, fromJust (lookup axiom_number axioms))
        | Axiom{..} <- pres_axioms ]

    lemma_proofs =
      Map.fromList [(lemma_id, tstp lemma_proof) | Lemma{..} <- pres_lemmas]

    goal_proofs =
      Map.fromList [(pg_number, tstp pg_proof) | ProvedGoal{..} <- pres_goals]

    tstp :: Proof (Extended Constant) -> Input Form
    tstp = deriv . derivation

    deriv :: Derivation (Extended Constant) -> Input Form
    deriv p@(Trans q r) = derivFrom (deriv r:sources q) p
    deriv p = derivFrom (sources p) p

    derivFrom :: [Input Form] -> Derivation (Extended Constant) -> Input Form
    derivFrom sources p =
      Input {
        tag = "step",
        kind = Jukebox.Axiom "axiom",
        what = jukeboxEquation (equation (certify p)),
        source =
          Inference "rw" "thm" sources }

    jukeboxEquation :: Equation (Extended Constant) -> Form
    jukeboxEquation (t :=: u) =
      toForm $ clause [Pos (jukeboxTerm ctx t Jukebox.:=: jukeboxTerm ctx u)]

    sources :: Derivation (Extended Constant) -> [Input Form]
    sources p =
      [ fromJust (Map.lookup lemma_id lemma_proofs)
      | Lemma{..} <- usortBy (comparing lemma_id) (usedLemmas p) ] ++
      [ fromJust (Map.lookup axiom_number axiom_proofs)
      | Axiom{..} <- usort (usedAxioms p) ]

main = do
  hSetBuffering stdout LineBuffering
  join . parseCommandLine "Twee, an equational theorem prover" .
    version ("twee version " ++ VERSION_twee) $
    globalFlags *> parseMainFlags *>
      -- hack: get --quiet and --no-proof options to appear before --tstp
    forAllFilesBox <*>
      (readProblemBox =>>=
       expert (toFof <$> clausifyBox <*> pure (tags True)) =>>=
       expert clausifyBox =>>=
       forAllConjecturesBox <*>
         (runTwee <$> globalFlags <*> tstpFlags <*> parseMainFlags <*> parseConfig <*> parsePrecedence))
