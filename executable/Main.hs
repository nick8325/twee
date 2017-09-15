{-# LANGUAGE CPP, RecordWildCards, FlexibleInstances, PatternGuards #-}
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
import Jukebox.Form hiding ((:=:), Var, Symbolic(..), Term, Axiom, size, Lemma)
import Jukebox.Tools.EncodeTypes
import Jukebox.TPTP.Print
import Jukebox.Tools.Clausify(ClausifyFlags(..), clausify)
import Jukebox.Tools.HornToUnit
import qualified Data.IntMap.Strict as IntMap
import System.IO
import System.Exit
import qualified Data.Set as Set

data MainFlags =
  MainFlags {
    flags_proof :: Bool,
    flags_trace :: Maybe (String, String) }

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
      flag "trace"
        ["Write a Prolog-format execution trace to this file (off by default)."]
        Nothing ((\x y -> Just (x, y)) <$> argFile <*> argModule)
    argModule = arg "<module>" "expected a Prolog module name" Just

parseConfig :: OptionParser Config
parseConfig =
  Config <$> maxSize <*> maxCPs <*> maxCPDepth <*> simplify <*> normPercent <*>
    (CP.Config <$> lweight <*> rweight <*> funweight <*> varweight <*> depthweight <*> dupcost <*> dupfactor) <*>
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
    normPercent =
      expert $
      inGroup "Completion heuristics" $
      defaultFlag "normalise-queue-percent" "Percent of time spent renormalising queued critical pairs" (cfg_renormalise_percent) argNum
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
        ["Test terms for subconnectedness (off by default)."]
        False
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
    con_arity :: {-# UNPACK #-} !Int,
    con_size  :: {-# UNPACK #-} !Int,
    con_bonus :: !Bool }
  deriving (Eq, Ord)

data Precedence = Precedence !Bool !Bool !(Maybe Int) !Int
  deriving (Eq, Ord)

instance Sized Constant where
  size Constant{..} = con_size
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

instance EqualsBonus Constant where
  hasEqualsBonus = con_bonus

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
      isEquals fun

isType :: Jukebox.Function -> Bool
isType fun = "$to_" `isPrefixOf` base (name fun)

isIfeq :: Jukebox.Function -> Bool
isIfeq fun = "$ifeq" `isPrefixOf` base (name fun)

isEquals :: Jukebox.Function -> Bool
isEquals fun = "$equals" `isPrefixOf` base (name fun)

jukeboxFunction :: TweeContext -> Extended Constant -> Jukebox.Function
jukeboxFunction _ (Function Constant{..}) = con_id
jukeboxFunction TweeContext{..} Minimal = ctx_minimal
jukeboxFunction TweeContext{..} (Skolem _) =
  error "Skolem variable leaked into rule"

tweeTerm :: HornFlags -> TweeContext -> (Jukebox.Function -> Precedence) -> Jukebox.Term -> Term (Extended Constant)
tweeTerm flags ctx prec t = build (tm t)
  where
    tm (Jukebox.Var (Unique x _ _ ::: _)) =
      var (V (fromIntegral x))
    tm (f :@: ts) =
      app (fun (tweeConstant flags ctx (prec f) f)) (map tm ts)

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
        []   -> indType
        [ty] -> ty

  var     <- newSymbol "X" ty
  minimal <- newFunction "$constant" [] ty
  true    <- newFunction "$true" [] ty
  false   <- newFunction "$false" [] ty
  equals  <- newFunction "$equals" [ty, ty] ty

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

runTwee :: GlobalFlags -> TSTPFlags -> MainFlags -> HornFlags -> Config -> [String] -> (IO () -> IO ()) -> Problem Clause -> IO Answer
runTwee globals (TSTPFlags tstp) main horn config precedence later obligs = {-# SCC runTwee #-} do
  let
    -- Encode whatever needs encoding in the problem
    ctx = makeContext obligs
    prob = addNarrowing ctx obligs

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
        (negate (funOcc c prob))

    -- Translate everything to Twee.
    toEquation (t, u) =
      canonicalise (tweeTerm horn ctx prec t :=: tweeTerm horn ctx prec u)

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
        presentToJukebox ctx (curry toEquation)
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
    else if configIsComplete config then Sat Satisfiable Nothing
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
        kind = Jukebox.Ax Jukebox.Axiom,
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
  let
    -- Never use splitting
    clausifyBox =
      pure (\prob -> return $! clausify (ClausifyFlags False) prob)
  hSetBuffering stdout LineBuffering
  join . parseCommandLine "Twee, an equational theorem prover" .
    version ("twee version " ++ VERSION_twee) $
    globalFlags *> parseMainFlags *>
      -- hack: get --quiet and --no-proof options to appear before --tstp
    forAllFilesBox <*>
      (readProblemBox =>>=
       expert clausifyBox =>>=
       forAllConjecturesBox <*>
         (combine <$>
           hornToUnitBox <*>
           (toFormulasBox =>>=
            expert (toFof <$> clausifyBox <*> pure (tags True)) =>>=
            clausifyBox =>>= oneConjectureBox) <*>
           (runTwee <$> globalFlags <*> tstpFlags <*> parseMainFlags <*> hornFlags <*> parseConfig <*> parsePrecedence)))
  where
    combine horn encode prove later prob = do
      res <- horn prob
      case res of
        Left ans -> return ans
        Right prob ->
          encode prob >>= prove later
