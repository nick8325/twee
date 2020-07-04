{-# LANGUAGE CPP, RecordWildCards, FlexibleInstances, PatternGuards #-}
{-# OPTIONS_GHC -flate-specialise #-}
module SequentialMain(main) where

import Control.Monad
import Data.Char
import Data.Either
import Twee hiding (message)
import Twee.Base hiding (char, lookup, vars, ground)
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
import Jukebox.Name hiding (lhs, rhs, label)
import qualified Jukebox.Form as Jukebox
import Jukebox.Form hiding ((:=:), Var, Symbolic(..), Term, Axiom, size, matchList)
import Jukebox.Tools.EncodeTypes
import Jukebox.TPTP.Print
import Jukebox.Tools.HornToUnit
import qualified Data.IntMap.Strict as IntMap
import System.IO
import System.Exit
import qualified Data.Set as Set
import qualified Twee.Label as Label

data MainFlags =
  MainFlags {
    flags_proof :: Bool,
    flags_trace :: Maybe (String, String),
    flags_formal_proof :: Bool,
    flags_explain_encoding :: Bool,
    flags_flip_ordering :: Bool,
    flags_give_up_on_saturation :: Bool }

parseMainFlags :: OptionParser MainFlags
parseMainFlags =
  MainFlags <$> proof <*> trace <*> formal <*> explain <*> flipOrdering <*> giveUp
  where
    proof =
      inGroup "Output options" $
      bool "proof" ["Produce proofs (on by default)."]
      True
    trace =
      expert $
      inGroup "Output options" $
      flag "trace"
        ["Write a Prolog-format execution trace to this file (off by default)."]
        Nothing ((\x y -> Just (x, y)) <$> argFile <*> argModule)
    formal =
      expert $
      inGroup "Output options" $
      bool "formal-proof" ["Print proof as formal TSTP derivation (requires --tstp; off by default)."] False
    explain =
      expert $
      inGroup "Output options" $
      bool "explain-encoding" ["In CASC mode, explain the conditional encoding (off by default)."] False
    flipOrdering =
      expert $
      inGroup "Term order options" $
      bool "flip-ordering" ["Make more common function symbols larger (off by default)."] False
    giveUp =
      expert $
      inGroup "Output options" $
      bool "give-up-on-saturation" ["Report SZS status GiveUp rather than Unsatisfiable on saturation (off by default)."] False
        
    argModule = arg "<module>" "expected a Prolog module name" Just

parseConfig :: OptionParser (Config (Extended Constant))
parseConfig =
  Config <$> maxSize <*> maxCPs <*> maxCPDepth <*> simplify <*> normPercent <*> cpSampleSize <*> cpRenormaliseThreshold <*> set_join_goals <*> always_simplify <*>
    (CP.Config <$> lweight <*> rweight <*> funweight <*> varweight <*> depthweight <*> dupcost <*> dupfactor) <*>
    (Join.Config <$> ground_join <*> connectedness <*> set_join) <*>
    (Proof.Config <$> all_lemmas <*> flat_proof <*> show_instances <*> show_axiom_uses)
  where
    maxSize =
      inGroup "Resource limits" $
      flag "max-term-size" ["Discard rewrite rules whose left-hand side is bigger than this limit (unlimited by default)."] Nothing (Just <$> checkSize <$> argNum)
    checkSize n t = size t <= n
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
    normPercent =
      expert $
      inGroup "Completion heuristics" $
      defaultFlag "normalise-queue-percent" "Percent of time spent renormalising queued critical pairs" cfg_renormalise_percent argNum
    cpSampleSize =
      expert $
      inGroup "Completion heuristics" $
      defaultFlag "cp-sample-size" "Size of random CP sample used to trigger renormalisation" cfg_cp_sample_size argNum
    cpRenormaliseThreshold =
      expert $
      inGroup "Completion heuristics" $
      defaultFlag "cp-renormalise-threshold" "Trigger renormalisation when this percentage of CPs can be simplified" cfg_renormalise_threshold argNum
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
    dupcost =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "dup-cost" "Cost of duplicate subterms" (CP.cfg_dupcost . cfg_critical_pairs) argNum
    dupfactor =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "dup-factor" "Size factor of duplicate subterms" (CP.cfg_dupfactor . cfg_critical_pairs) argNum
    ground_join =
      expert $
      inGroup "Critical pair joining heuristics" $
      bool "ground-joining"
        ["Test terms for ground joinability (on by default)."]
        True
    connectedness =
      expert $
      inGroup "Critical pair joining heuristics" $
      bool "connectedness"
        ["Test terms for subconnectedness (on by default)."]
        True
    set_join =
      expert $
      inGroup "Critical pair joining heuristics" $
      bool "set-join"
        ["Compute all normal forms when joining critical pairs (off by default)."]
        False
    set_join_goals =
      expert $
      inGroup "Critical pair joining heuristics" $
      bool "set-join-goals"
        ["Compute all normal forms when joining goal terms (on by default)."]
        True
    always_simplify =
      expert $
      inGroup "Debugging options" $
      bool "always-simplify"
        ["Interreduce rules after every step."]
        False
    all_lemmas =
      inGroup "Proof presentation" $
      bool "all-lemmas"
        ["Produce a proof with one lemma for each critical pair (off by default)."]
        False
    flat_proof =
      inGroup "Proof presentation" $
      bool "no-lemmas"
        ["Produce a proof with no lemmas (off by default).",
         "May lead to exponentially large proofs."]
        False
    show_instances =
      inGroup "Proof presentation" $
      bool "show-instances"
        ["Show which instance of a lemma or axiom each rewrite step uses (off by default)."]
        False
    show_axiom_uses =
      inGroup "Proof presentation" $
      interpret <$>
      concat <$>
      manyFlags "show-uses-of"
        ["Show which instances of the given axioms were needed (none by default).",
         "Separate multiple axiom names with commas.",
         "Use --show-uses-of all to show uses of all axioms."]
        (splitOn "," <$> arg "<axioms>" "expected a list of axiom names" Just)
      where
        interpret xss ax = axiom_name ax `elem` xss || "all" `elem` xss
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
    con_arity :: {-# UNPACK #-} !Int,
    con_size  :: {-# UNPACK #-} !Int,
    con_bonus :: !Bool }
  deriving (Eq, Ord)

data Precedence = Precedence !Bool !Bool !(Maybe Int) !Int
  deriving (Eq, Ord)

instance Labelled Constant where
  label = fromIntegral . Label.labelNum . Label.label
  find = Label.find . Label.unsafeMkLabel . fromIntegral

instance Sized Constant where
  size Constant{..} = con_size
instance Arity Constant where
  arity Constant{..} = con_arity

instance Pretty Constant where
  pPrint Constant{..} = text (base con_id)

instance PrettyTerm Constant where
  termStyle Constant{..}
    | hasLabel "type_tag" con_id = invisible
    | any isAlphaNum (base con_id) = uncurried
    | otherwise =
      case con_arity of
        1 -> prefix
        2 -> infixStyle 5
        _ -> uncurried

instance Ordered (Extended Constant) where
  lessEq t u = KBO.lessEq t u
  lessIn model t u = KBO.lessIn model t u

instance EqualsBonus Constant where
  hasEqualsBonus = con_bonus
  isEquals = SequentialMain.isEquals . con_id
  isTrue = SequentialMain.isTrue . con_id
  isFalse = SequentialMain.isFalse . con_id

data TweeContext =
  TweeContext {
    ctx_var     :: Jukebox.Variable,
    ctx_minimal :: Jukebox.Function,
    ctx_true    :: Jukebox.Function,
    ctx_false   :: Jukebox.Function,
    ctx_equals  :: Jukebox.Function,
    ctx_type    :: Type }

-- Convert back and forth between Twee and Jukebox.
tweeConstant :: HornFlags -> TweeContext -> Precedence -> Jukebox.Function -> Extended Constant
tweeConstant flags TweeContext{..} prec fun
  | fun == ctx_minimal = Minimal
  | otherwise = Function (Constant prec fun (Jukebox.arity fun) (sz fun) (bonus fun))
  where
    sz fun = if isType fun then 0 else 1
    bonus fun =
      (isIfeq fun && encoding flags /= Asymmetric2) ||
      SequentialMain.isEquals fun

isType :: Jukebox.Function -> Bool
isType fun =
  hasLabel "type_tag" (name fun) && Jukebox.arity fun == 1

isIfeq :: Jukebox.Function -> Bool
isIfeq fun =
  hasLabel "ifeq" (name fun)

isEquals :: Jukebox.Function -> Bool
isEquals fun =
  hasLabel "equals" (name fun) && Jukebox.arity fun == 2

isTrue :: Jukebox.Function -> Bool
isTrue fun =
  hasLabel "true" (name fun) && Jukebox.arity fun == 0

isFalse :: Jukebox.Function -> Bool
isFalse fun =
  hasLabel "false" (name fun) && Jukebox.arity fun == 0

jukeboxFunction :: TweeContext -> Extended Constant -> Jukebox.Function
jukeboxFunction _ (Function Constant{..}) = con_id
jukeboxFunction TweeContext{..} Minimal = ctx_minimal
jukeboxFunction TweeContext{..} (Skolem _) =
  error "Skolem variable leaked into rule"

tweeTerm :: HornFlags -> TweeContext -> (Jukebox.Function -> Precedence) -> Jukebox.Term -> Term (Extended Constant)
tweeTerm flags ctx prec t = build (tm t)
  where
    tm (Jukebox.Var (x ::: _)) =
      var (V (fromIntegral (Label.labelNum (Label.label x))))
    tm (f :@: ts) =
      app (fun (tweeConstant flags ctx (prec f) f)) (map tm ts)

jukeboxTerm :: TweeContext -> Term (Extended Constant) -> Jukebox.Term
jukeboxTerm TweeContext{..} (Var (V x)) =
  Jukebox.Var (Unique (fromIntegral x) "X" Nothing defaultRenamer ::: ctx_type)
jukeboxTerm ctx@TweeContext{..} (App f t) =
  jukeboxFunction ctx (fun_value f) :@: map (jukeboxTerm ctx) ts
  where
    ts = unpack t

makeContext :: Problem Clause -> TweeContext
makeContext prob = run prob $ \prob -> do
  let
    ty =
      case types' prob of
        []   -> indType
        [ty] -> ty

  var     <- newSymbol "X" ty
  minimal <- newFunction (withLabel "minimal" (name "constant")) [] ty
  true    <- newFunction (withLabel "true" (name "true")) [] ty
  false   <- newFunction (withLabel "false" (name "false")) [] ty
  equals  <- newFunction (withLabel "equals" (name "equals")) [ty, ty] ty

  return TweeContext {
    ctx_var = var,
    ctx_minimal = minimal,
    ctx_true = true,
    ctx_false = false,
    ctx_equals = equals,
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
              kind = Jukebox.Ax NegatedConjecture,
              what =
                let form = And (map (Literal . snd) equalityLiterals) in
                ForAll (Bind (Set.fromList (vars form)) form),
              source =
                Inference "encode_existential" "esa"
                  (map (fmap toForm . fst) nonGroundGoals) }

          input tag form =
            Input {
              tag = tag,
              kind = Conj Conjecture,
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

runTwee :: GlobalFlags -> TSTPFlags -> HornFlags -> [String] -> Config (Extended Constant) -> MainFlags -> (IO () -> IO ()) -> Problem Clause -> IO Answer
runTwee globals (TSTPFlags tstp) horn precedence config MainFlags{..} later obligs = {-# SCC runTwee #-} do
  let
    -- Encode whatever needs encoding in the problem
    ctx = makeContext obligs
    prob = prettyNames (addNarrowing ctx obligs)

  (axioms0, goals0) <-
    case identifyProblem ctx prob of
      Left inp -> do
        mapM_ (hPutStrLn stderr) [
          "The problem contains the following clause, which is not a unit equality:",
          indent (show (pPrintClauses [inp])),
          "Twee only handles unit equality problems."]
        exitWith (ExitFailure 1)
      Right x -> return x

  let
    -- Work out a precedence for function symbols
    prec c =
      Precedence
        (isType c)
        (isNothing (elemIndex (base c) precedence))
        (fmap negate (elemIndex (base c) precedence))
        (maybeNegate (Map.findWithDefault 0 c occs))
    maybeNegate = if flags_flip_ordering then id else negate
    occs = funsOcc prob

    -- Translate everything to Twee.
    toEquation (t, u) =
      canonicalise (tweeTerm horn ctx prec t :=: tweeTerm horn ctx prec u)

    goals =
      [ goal n pre_name (toEquation pre_eqn)
      | (n, PreEquation{..}) <- zip [1..] goals0 ]
    axioms =
      [ Axiom n pre_name (toEquation pre_eqn)
      | (n, PreEquation{..}) <- zip [1..] axioms0 ]

    withGoals = foldl' (addGoal config) (initialState config) goals
    withAxioms = foldl' (addAxiom config) withGoals axioms

  -- Set up tracing.
  sayTrace <-
    case flags_trace of
      Nothing -> return $ \_ -> return ()
      Just (file, mod) -> do
        h <- openFile file WriteMode
        hSetBuffering h LineBuffering
        let put msg = hPutStrLn h msg
        put $ ":- module(" ++ mod ++ ", [step/1, lemma/1])."
        put ":- discontiguous(step/1)."
        put ":- discontiguous(lemma/1)."
        put ":- style_check(-singleton)."
        return $ \msg -> hPutStrLn h msg
  
  let
    say msg = unless (quiet globals) (putStrLn msg)
    line = say ""
    output = Output {
      output_message = \msg -> do
        say (prettyShow msg)
        sayTrace (show (traceMsg msg)) }

    traceMsg (NewActive active) =
      step "add" [traceActive active]
    traceMsg (NewEquation eqn) =
      step "hard" [traceEqn eqn]
    traceMsg (DeleteActive active) =
      step "delete" [traceActive active]
    traceMsg SimplifyQueue =
      step "simplify_queue" []
    traceMsg Interreduce =
      step "interreduce" []

    traceActive Active{..} =
      traceApp "rule" [pPrint active_id, traceEqn (unorient active_rule)]
    traceEqn (t :=: u) =
      pPrintPrec prettyNormal 6 t <+> text "=" <+> pPrintPrec prettyNormal 6 u
    traceApp f xs =
      pPrintTerm uncurried prettyNormal 0 (text f) xs

    step :: String -> [Doc] -> Doc
    step f xs = traceApp "step" [traceApp f xs] <#> text "."

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

  when (solved state && flags_proof) $ later $ do
    let
      cfg_present
        | tstp && flags_formal_proof =
          (cfg_proof_presentation config){cfg_all_lemmas = True}
        | otherwise =
          cfg_proof_presentation config
      pres = present cfg_present (solutions state)

    sayTrace ""
    forM_ (pres_lemmas pres) $ \p ->
      sayTrace $ show $
        traceApp "lemma" [traceEqn (equation p)] <#> text "."

    when (tstp && not flags_formal_proof) $ do
      putStrLn "% SZS output start Proof"
      let
        axiomForms =
          Map.fromList
            (zip (map axiom_number axioms) (map pre_form axioms0))
        goalForms =
          Map.fromList
            (zip (map goal_number goals) (map pre_form goals0))

        findSource forms n =
          case Map.lookup n forms of
            Nothing -> []
            Just inp -> go inp
           where
            go Input{source = Unknown} = []
            go Input{source = Inference _ _ inps} = concatMap go inps
            go inp@Input{source = FromFile _ _} = [inp]

      when flags_explain_encoding $ do
        putStrLn "Take the following subset of the input axioms:"
        mapM_ putStrLn $ map ("  " ++) $ lines $ showProblem $
          usortBy (comparing show) $
            (pres_axioms pres >>= findSource axiomForms . axiom_number) ++
            (pres_goals pres >>= findSource goalForms . pg_number)

        putStrLn ""
        putStrLn "Now clausify the problem and encode Horn clauses using encoding 3 of"
        putStrLn "http://www.cse.chalmers.se/~nicsma/papers/horn.pdf."
        putStrLn "We repeatedly replace C & s=t => u=v by the two clauses:"
        putStrLn "  fresh(y, y, x1...xn) = u"
        putStrLn "  C => fresh(s, t, x1...xn) = v"
        putStrLn "where fresh is a fresh function symbol and x1..xn are the free"
        putStrLn "variables of u and v."
        putStrLn "A predicate p(X) is encoded as p(X)=true (this is sound, because the"
        putStrLn "input problem has no model of domain size 1)."
        putStrLn ""
        putStrLn "The encoding turns the above axioms into the following unit equations and goals:"
        putStrLn ""
      print $ pPrintPresentation (cfg_proof_presentation config) pres
      putStrLn "% SZS output end Proof"
      putStrLn ""
  
    when (tstp && flags_formal_proof) $ do
      putStrLn "% SZS output start CNFRefutation"
      print $ pPrintProof $
        presentToJukebox ctx (curry toEquation)
          (zip (map axiom_number axioms) (map pre_form axioms0))
          (zip (map goal_number goals) (map pre_form goals0))
          pres
      putStrLn "% SZS output end CNFRefutation"
      putStrLn ""

    unless tstp $ do
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

    when (tstp && configIsComplete config) $ do
      putStrLn "% SZS output start Saturation"
      print $ pPrintProof $
        map pre_form axioms0 ++
        map pre_form goals0 ++
        [ Input "rule" (Jukebox.Ax Jukebox.Axiom) Unknown $
            toForm $ clause
              [Pos (jukeboxTerm ctx (lhs rule) Jukebox.:=: jukeboxTerm ctx (rhs rule))]
        | rule <- rules state ]
      putStrLn "% SZS output end Saturation"
      putStrLn ""

    if configIsComplete config then do
      putStrLn "Ran out of critical pairs. This means the conjecture is not true."
    else do
      putStrLn "Gave up on reaching the given resource limit."
    putStrLn "Here is the final rewrite system:"
    forM_ actives $ \active ->
      putStrLn ("  " ++ prettyShow (canonicalise (active_rule active)))
    putStrLn ""

  return $
    if solved state then Unsat Unsatisfiable Nothing
    else if configIsComplete config && not (dropNonHorn horn) && not flags_give_up_on_saturation then Sat Satisfiable Nothing
    else NoAnswer GaveUp

-- Transform a proof presentation into a Jukebox proof.
presentToJukebox ::
  TweeContext ->
  (Jukebox.Term -> Jukebox.Term -> Equation (Extended Constant)) ->
  -- Axioms, indexed by axiom number.
  [(Int, Input Form)] ->
  -- N.B. the formula here proves the negated goal.
  [(Int, Input Form)] ->
  Presentation (Extended Constant) ->
  Problem Form
presentToJukebox ctx toEquation axioms goals Presentation{..} =
  [ Input {
      tag = pg_name,
      kind = Jukebox.Ax Jukebox.Axiom,
      what = false,
      source =
        Inference "resolution" "thm"
          [-- A proof of t != u
           existentialHack pg_goal_hint (fromJust (lookup pg_number goals)),
           -- A proof of t = u
           fromJust (Map.lookup pg_number goal_proofs)] }
  | ProvedGoal{..} <- pres_goals ]

  where
    axiom_proofs =
      Map.fromList
        [ (axiom_number, fromJust (lookup axiom_number axioms))
        | Axiom{..} <- pres_axioms ]

    lemma_proofs =
      Map.fromList [(p, tstp p) | p <- pres_lemmas]

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
        kind = Jukebox.Ax Jukebox.Axiom,
        what = jukeboxEquation (equation (certify p)),
        source =
          Inference "rw" "thm" sources }

    jukeboxEquation :: Equation (Extended Constant) -> Form
    jukeboxEquation (t :=: u) =
      toForm $ clause [Pos (jukeboxTerm ctx t Jukebox.:=: jukeboxTerm ctx u)]

    sources :: Derivation (Extended Constant) -> [Input Form]
    sources p =
      [ fromJust (Map.lookup lemma lemma_proofs)
      | lemma <- usort (usedLemmas p) ] ++
      [ fromJust (Map.lookup axiom_number axiom_proofs)
      | Axiom{..} <- usort (usedAxioms p) ]

    -- An ugly hack: since Twee.Proof decodes $true = $false into a
    -- proof of the existentially quantified goal, we need to do the
    -- same decoding at the Jukebox level.
    existentialHack eqn input =
      case find input of
        [] -> error $ "bug in TSTP output: can't fix up decoded existential"
        (inp:_) -> inp
        where
          -- Check if this looks like the correct clause;
          -- if not, try its ancestors.
          find inp | ok inp = [inp]
          find Input{source = Inference _ _ inps} =
            concatMap find inps
          find _ = []

          ok inp =
            case toClause (what inp) of
              Nothing -> False
              Just (Clause (Bind _ [Neg (t' Jukebox.:=: u')])) ->
                let
                  eqn' = toEquation t' u'
                  ts = buildList [eqn_lhs eqn, eqn_rhs eqn]
                  us = buildList [eqn_lhs eqn', eqn_rhs eqn']
                in
                  isJust (matchList ts us) && isJust (matchList us ts)

main = do
  hSetBuffering stdout LineBuffering
  join . parseCommandLineWithExtraArgs
    ["--no-conjunctive-conjectures", "--no-split"]
#ifdef VERSION_twee
    "Twee, an equational theorem prover" . version ("twee version " ++ VERSION_twee) $
#else
    "Twee, an equational theorem prover" . version "twee development version" $
#endif
      globalFlags *> parseMainFlags *>
      -- hack: get --quiet and --no-proof options to appear before --tstp
      forAllFilesBox <*>
        (readProblemBox =>>=
         expert clausifyBox =>>=
         forAllConjecturesBox <*>
           (combine <$>
             expert hornToUnitBox <*>
             parseConfig <*>
             parseMainFlags <*>
             (toFormulasBox =>>=
              expert (toFof <$> clausifyBox <*> pure (tags True)) =>>=
              expert clausifyBox =>>= expert oneConjectureBox) <*>
             (runTwee <$> globalFlags <*> tstpFlags <*> expert hornFlags <*> parsePrecedence)))
  where
    combine horn config main encode prove later prob0 = do
      res <- horn prob0
      case res of
        Left ans -> return ans
        Right prob -> do
          let
            isUnitEquality [Pos (_ Jukebox.:=: _)] = True
            isUnitEquality [Neg (_ Jukebox.:=: _)] = True
            isUnitEquality _ = False
            isUnit = all isUnitEquality (map (toLiterals . what) prob0)
            main' = if isUnit then main else main{flags_formal_proof = False}
          encode prob >>= prove config main' later
