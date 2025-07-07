{-# LANGUAGE CPP, RecordWildCards, FlexibleInstances, PatternGuards, DeriveAnyClass, RankNTypes #-}
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
import Jukebox.Form hiding ((:=:), Var, Symbolic(..), Term, Axiom, size, Subst, subst)
import Jukebox.Tools.EncodeTypes
import Jukebox.TPTP.Print
import Jukebox.Tools.HornToUnit
import qualified Data.IntMap.Strict as IntMap
import System.IO
import System.Exit
import qualified Data.Set as Set
import qualified Data.Label as Label
import System.Console.ANSI
import Data.Symbol
import Twee.Profile

data MainFlags =
  MainFlags {
    flags_proof :: Bool,
    flags_trace :: Maybe (String, String),
    flags_formal_proof :: Bool,
    flags_explain_encoding :: Bool,
    flags_flip_ordering :: Bool,
    flags_give_up_on_saturation :: Bool,
    flags_flatten_goals :: Bool,
    flags_flatten_nonground :: Bool,
    flags_flatten_goals_lightly :: Bool,
    flags_flatten_all :: Bool,
    flags_flatten_regeneralise :: Bool,
    flags_eliminate :: [String],
    flags_backwards_goal :: Int,
    flags_flatten_backwards_goal :: Int,
    flags_equals_transformation :: Bool,
    flags_distributivity_heuristic :: Bool,
    flags_kbo_weight0 :: Bool,
    flags_goal_heuristic :: Bool }

parseMainFlags :: OptionParser MainFlags
parseMainFlags =
  MainFlags <$> proof <*> trace <*> formal <*> explain <*> flipOrdering <*> giveUp <*> flatten <*> flattenNonGround <*> flattenLightly <*> flattenAll <*> flattenRegeneralise <*> eliminate <*> backwardsGoal <*> flattenBackwardsGoal <*> equalsTransformation <*> distributivityHeuristic <*> kboWeight0 <*> goalHeuristic
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
      bool "flip-ordering" ["Make more common function symbols smaller (off by default)."] False
    kboWeight0 =
      expert $
      inGroup "Term order options" $
      bool "kbo-weight0" ["Give functions of arity >= 2 a weight of 0."] False
    giveUp =
      expert $
      inGroup "Output options" $
      bool "give-up-on-saturation" ["Report SZS status GiveUp rather than Unsatisfiable on saturation (off by default)."] False
    flatten =
      expert $
      inGroup "Completion heuristics" $
      bool "flatten-goal" ["Flatten goal by adding new axioms (on by default)."] True
    flattenNonGround =
      expert $
      inGroup "Completion heuristics" $
      bool "flatten-nonground" ["Flatten even non-ground clauses (off by default)."] False
    flattenLightly =
      expert $
      inGroup "Completion heuristics" $
      bool "flatten-goal-lightly" ["Flatten goal non-recursively by adding new axioms (off by default)."] False
    flattenAll =
      expert $
      inGroup "Completion heuristics" $
      bool "flatten" ["Flatten all clauses by adding new axioms (off by default)."] False
    flattenRegeneralise =
      expert $
      inGroup "Completion heuristics" $
      bool "flatten-regeneralise" ["Regeneralise rules involving flattened goal terms (off by default)."] False
    backwardsGoal =
      expert $
      inGroup "Completion heuristics" $
      flag "backwards-goal" ["Try rewriting backwards from the goal this many times (0 by default)."] 0 argNum
    flattenBackwardsGoal =
      expert $
      inGroup "Completion heuristics" $
      flag "flatten-backwards-goal" ["Try rewriting backwards from the goal this many times when flattening (0 by default)."] 0 argNum
    equalsTransformation =
      expert $
      inGroup "Completion heuristics" $
      bool "equals-transformation" ["Apply the 'equals transformation' even to ground goals (off by default)."] False
    distributivityHeuristic =
      expert $
      inGroup "Completion heuristics" $
      bool "distributivity-heuristic" ["Treat distributive operators specially (off by default)."] False
    goalHeuristic =
      expert $
      inGroup "Completion heuristics" $
      bool "goal-heuristic" ["Use the CP weighting heuristic from Anantharaman and Andrianarievelo (off by default)."] False
    eliminate =
      inGroup "Proof presentation" $
      concat <$>
      manyFlags "eliminate"
        ["Treat these axioms as definitions and eliminate them from the proof.",
         "The axiom must have the shape f(x1...xn) = t, where x1...xn are",
         "distinct variables. The term f must not otherwise appear in the problem!",
         "This is not checked."]
        (splitOn "," <$> arg "<axioms>" "expected a list of axiom names" Just)

    argModule = arg "<module>" "expected a Prolog module name" Just

parseConfig :: OptionParser (Config Constant)
parseConfig =
  Config <$> maxSize <*> maxCPs <*> maxCPDepth <*> maxRules <*> simplify <*> normPercent <*> cpSampleSize <*> cpRenormaliseThreshold <*> set_join_goals <*> always_simplify <*> complete_subsets <*>
    pure undefined <*> -- scoring function - filled in later, in runTwee
    (Join.Config <$> ground_join <*> connectedness <*> ground_connectedness <*> set_join <*> ground_join_limit <*> ground_join_incomplete_limit) <*>
    (Proof.Config <$> all_lemmas <*> flat_proof <*> ground_proof <*> show_instances <*> colour <*> show_axiom_uses <*> show_peaks <*> eliminate_existentials_coding) <*> pure [] <*> randomMode <*> randomModeGoalDirected <*> randomModeSimple <*> randomModeBestOf <*> alwaysComplete
  where
    maxSize =
      inGroup "Resource limits" $
      flag "max-term-size" ["Discard rewrite rules whose left-hand side is bigger than this limit (unlimited by default)."] Nothing (Just <$> checkSize <$> argNum)
    checkSize n t = KBO.size t <= n
    maxCPs =
      inGroup "Resource limits" $
      flag "max-cps" ["Give up after considering this many critical pairs (unlimited by default)."] maxBound argNum
    maxCPDepth =
      inGroup "Resource limits" $
      flag "max-cp-depth" ["Only consider critical pairs up to this depth (unlimited by default)."] maxBound argNum
    maxRules =
      inGroup "Resource limits" $
      flag "max-rules" ["Give up after generating this many rules (unlimited by default)."] maxBound argNum
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
    ground_join =
      expert $
      inGroup "Critical pair joining heuristics" $
      bool "ground-joining"
        ["Test terms for ground joinability (on by default)."]
        True
    ground_join_limit =
      inGroup "Critical pair joining heuristics" $
      flag "ground-joining-limit" ["Assume not ground joinable after considering this many orderings (unlimited by default)."] maxBound argNum
    ground_join_incomplete_limit =
      inGroup "Critical pair joining heuristics" $
      flag "ground-joining-incomplete-limit" ["Assume ground joinable after considering this many orderings (unlimited by default)."] maxBound argNum
    connectedness =
      expert $
      inGroup "Critical pair joining heuristics" $
      bool "connectedness"
        ["Test terms for subconnectedness, as a separate check (on by default)."]
        True
    ground_connectedness =
      expert $
      inGroup "Critical pair joining heuristics" $
      bool "ground-connectedness"
        ["Test terms for subconnectedness, as part of ground joinability testing (off by default)."]
        False
    complete_subsets =
      expert $
      inGroup "Critical pair joining heuristics" $
      bool "complete-subsets"
        ["Identify and exploit complete subsets of the axioms in joining (off by default)."]
        False
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
    ground_proof =
      inGroup "Proof presentation" $
      bool "ground-proof"
        ["Produce a ground proof (off by default).",
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
    show_peaks =
      inGroup "Proof presentation" $
      bool "show-peaks"
        ["Show peak terms in a proof (off by default)."]
        False
    eliminate_existentials_coding =
      inGroup "Proof presentation" $
      bool "eliminate-existentials-coding"
        ["Eliminate $equals from proofs (on by default)."]
        True
    randomMode =
      expert $
      inGroup "Completion heuristics" $
      bool "random-mode"
        ["Use random testing to find suitable CPs (doesn't work yet!) (off by default)."]
        False
    randomModeGoalDirected =
      expert $
      inGroup "Completion heuristics" $
      bool "random-mode-goal-directed"
        ["Use goal-direction in --random-mode (off by default)."]
        False
    randomModeSimple =
      expert $
      inGroup "Completion heuristics" $
      bool "random-mode-simple"
        ["Use simple version of --random-mode (off by default)."]
        False
    randomModeBestOf =
      inGroup "Completion heuristics" $
      defaultFlag "random-mode-best-of" "Generate this many critical pairs at a time and pick the best one" cfg_random_mode_best_of argNum
    alwaysComplete =
      inGroup "Input and clausifier options" $
      bool "complete"
        ["Don't stop until the rewrite system is confluent"]
        False
    colour = fromMaybe <$> io colourSupported <*> colourFlag
    colourFlag =
      inGroup "Proof presentation" $
      primFlag "(no-)colour"
        ["Produce output in colour (on by default if writing output to a terminal)."]
        (`elem` map fst colourFlags)
        (\_ y -> return y)
        Nothing
        (pure (`lookup` colourFlags))
    colourFlags = [("--colour", True), ("--no-colour", False),
                   ("--color", True), ("--no-color", False)]
    colourSupported =
      liftM2 (&&) (hSupportsANSIColor stdout)
        (return (setSGRCode [] /= "")) -- Check for Windows terminal not supporting ANSI

    defaultFlag :: Show a => String -> String -> (Config Constant -> a) -> ArgParser a -> OptionParser a
    defaultFlag name desc field parser =
      flag name [desc ++ " (" ++ show def ++ " by default)."] def parser
      where
        def = field defaultConfig

parseCPConfig :: OptionParser CP.Config
parseCPConfig =
  CP.Config <$> lweight <*> rweight <*> funweight <*> varweight <*> depthweight <*> dupcost <*> dupfactor
  where
    lweight =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "lhs-weight" "Weight given to LHS of critical pair" CP.cfg_lhsweight argNum
    rweight =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "rhs-weight" "Weight given to RHS of critical pair" CP.cfg_rhsweight argNum
    funweight =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "fun-weight" "Weight given to function symbols" CP.cfg_funweight argNum
    varweight =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "var-weight" "Weight given to variable symbols" CP.cfg_varweight argNum
    depthweight =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "depth-weight" "Weight given to critical pair depth" CP.cfg_depthweight argNum
    dupcost =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "dup-cost" "Cost of duplicate subterms" CP.cfg_dupcost argNum
    dupfactor =
      expert $
      inGroup "Critical pair weighting heuristics" $
      defaultFlag "dup-factor" "Size factor of duplicate subterms" CP.cfg_dupfactor argNum

    defaultFlag name desc field parser =
      flag name [desc ++ " (" ++ show def ++ " by default)."] def parser
      where
        def = field CP.defaultConfig

parsePrecedence :: OptionParser [String]
parsePrecedence =
  expert $
  inGroup "Term order options" $
  fmap (splitOn ",")
  (flag "precedence" ["List of functions in descending order of precedence."] [] (arg "<function>" "expected a function name" Just))

data Constant =
  Minimal |
  Skolem Int |
  Constant {
    con_prec   :: {-# UNPACK #-} !Precedence,
    con_id     :: {-# UNPACK #-} !Jukebox.Function,
    con_arity  :: {-# UNPACK #-} !Int,
    con_size   :: !Integer,
    con_weight :: !Integer,
    con_bonus  :: !Bool }
  deriving (Eq, Ord, Labelled)

data Precedence = Precedence !Bool !Bool !Bool !(Maybe Int) !Int
  deriving (Eq, Ord)

instance KBO.Sized Constant where
  size Minimal = 1
  size Skolem{} = 1
  size Constant{..} = con_size
instance KBO.Weighted Constant where
  argWeight Minimal = 1
  argWeight Skolem{} = 1
  argWeight Constant{..} = con_weight

instance Pretty Constant where
  pPrint Minimal = text "?"
  pPrint (Skolem n) = text ("sk" ++ show n)
  pPrint Constant{..} = text (removePostfix (base con_id))
    where
      removePostfix ('_':x:xs) | con_arity == 1 = x:xs
      removePostfix xs = xs

instance PrettyTerm Constant where
  termStyle Minimal = uncurried
  termStyle Skolem{} = uncurried
  termStyle Constant{..}
    | hasLabel "type_tag" con_id = invisible
    | "_" `isPrefixOf` base con_id && con_arity == 1 = postfix
    | any isAlphaNum (base con_id) = uncurried
    | otherwise =
      case con_arity of
        1 -> prefix
        2 -> infixStyle 5
        _ -> uncurried

instance Minimal Constant where
  minimal = fun Minimal
  skolem = fun . Skolem

instance Ordered Constant where
  lessEq t u = KBO.lessEq t u
  lessIn model t u = KBO.lessIn model t u
  lessEqSkolem t u = KBO.lessEqSkolem t u

instance EqualsBonus Constant where
  hasEqualsBonus Minimal = False
  hasEqualsBonus Skolem{} = False
  hasEqualsBonus c = con_bonus c
  isEquals Minimal = False
  isEquals Skolem{} = False
  isEquals c = SequentialMain.isEquals (con_id c)
  isTrue Minimal = False
  isTrue Skolem{} = False
  isTrue c = SequentialMain.isTrue (con_id c)
  isFalse Minimal = False
  isFalse Skolem{} = False
  isFalse c = SequentialMain.isFalse (con_id c)

data TweeContext =
  TweeContext {
    ctx_var     :: Jukebox.Variable,
    ctx_minimal :: Jukebox.Function,
    ctx_true    :: Jukebox.Function,
    ctx_false   :: Jukebox.Function,
    ctx_equals  :: Jukebox.Function,
    ctx_type    :: Type }

-- Convert back and forth between Twee and Jukebox.
tweeConstant :: MainFlags -> HornFlags -> TweeContext -> Precedence -> Jukebox.Function -> Constant
tweeConstant MainFlags{..} flags TweeContext{..} prec fun
  | fun == ctx_minimal = Minimal
  | otherwise =
    Constant {
      con_prec = prec,
      con_id = fun,
      con_arity = Jukebox.arity fun,
      con_size = if flags_kbo_weight0 && Jukebox.arity fun >= 2 then 0 else if isInv then 0 else 1,
      con_weight = 1,
      con_bonus = bonus fun }
  where
    bonus fun =
      (isIfeq fun && encoding flags /= Asymmetric2) ||
      SequentialMain.isEquals fun
    isInv =
      case prec of
        Precedence _ x _ _ _ -> x

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

jukeboxFunction :: TweeContext -> Constant -> Jukebox.Function
jukeboxFunction _ Constant{..} = con_id
jukeboxFunction TweeContext{..} Minimal = ctx_minimal

tweeTerm :: MainFlags -> HornFlags -> TweeContext -> (Jukebox.Function -> Precedence) -> Jukebox.Term -> Term Constant
tweeTerm flags horn ctx prec t = build (tm t)
  where
    tm (Jukebox.Var (x ::: _)) =
      var (V (fromIntegral (Label.labelNum (Label.label x))))
    tm (f :@: ts) =
      app (fun (tweeConstant flags horn ctx (prec f) f)) (map tm ts)

jukeboxTerm :: TweeContext -> Term Constant -> Jukebox.Term
jukeboxTerm TweeContext{..} (Var (V x)) =
  Jukebox.Var (Unique (fromIntegral x) (intern "X") Nothing defaultRenamer ::: ctx_type)
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

flattenGoals :: Int -> Bool -> Bool -> Bool -> Problem Clause -> Problem Clause
flattenGoals backwardsGoal flattenNonGround flattenAll full prob =
  run prob $ \prob -> do
    let ts = usort $ extraTerms prob
    cs <- mapM define ts
    return (prob ++ cs)
  where
    extraTerms prob = concatMap (input prob) prob
    input prob Input{what = Clause (Bind _ [Neg (x Jukebox.:=: y)])} =
      concatMap term (backwards backwardsGoal prob x) ++
      concatMap term (backwards backwardsGoal prob y)
    input _ Input{what = Clause (Bind _ [Pos (x Jukebox.:=: y)])}
      | flattenAll = term x ++ term y
    input _ _ = []

    term t@(_f :@: ts) =
      [ t
      | ground t || flattenNonGround,
        not (all isVar ts) || usort ts /= sort ts ] ++
      if full then concatMap term ts else []
    term _ = []

    isVar (Jukebox.Var _) = True
    isVar _ = False

    define (f :@: ts) = do
      name <- newName f
      let vs  = Jukebox.vars ts
          g = name ::: FunType (map typ vs) (typ f)
          c = clause [Pos (g :@: map Jukebox.Var vs Jukebox.:=: f :@: ts)]
      return Input{ident = Nothing, tag = "flattening", kind = Jukebox.Ax Definition,
                   what = c, source = Unknown }

    backwards 0 _ t = [t]
    backwards n cs t =
      t:
      [ v
      | Input{what = Clause (Bind _ [Pos (x0 Jukebox.:=: y0)])} <- cs,
        (x, y) <- [(x0, y0), (y0, x0)],
        (s, k) <- contexts t,
        sub <- maybeToList (Jukebox.match x s),
        let u = k (Jukebox.subst sub y),
        ground u,
        v <- backwards (n-1) cs u ]

addDistributivityHeuristic :: Problem Clause -> Problem Clause
addDistributivityHeuristic prob =
  run prob $ \prob -> do
    cs <- mapM add prob
    return (prob ++ catMaybes cs)

  where
    add Input{what = Clause (Bind _ [Pos (t Jukebox.:=: u)])} =
      case checkDistributivity t u `mplus` checkDistributivity u t of
        Just (f, g, ty) -> do
          name <- newName (base f ++ "_" ++ base g)
          x <- Jukebox.Var <$> newSymbol "X" ty
          y <- Jukebox.Var <$> newSymbol "Y" ty
          z <- Jukebox.Var <$> newSymbol "Z" ty
          Just <$> define name (g :@: [f :@: [x, y], z])
        _ -> return Nothing
    add _ = return Nothing

    checkDistributivity
      (f1 :@: [Jukebox.Var x1, g1 :@: [Jukebox.Var y1, Jukebox.Var z1]])
      (g2 :@: [f2 :@: [Jukebox.Var x2, Jukebox.Var y2],
               f3 :@: [Jukebox.Var x3, Jukebox.Var z2]])
      | f1 == f2 && f2 == f3 && g1 == g2 &&
        x1 == x2 && x2 == x3 && y1 == y2 && z1 == z2 =
        Just (f1, g1, Jukebox.typ x1)
      
    checkDistributivity
      (f1 :@: [g1 :@: [Jukebox.Var x1, Jukebox.Var y1], Jukebox.Var z1])
      (g2 :@: [f2 :@: [Jukebox.Var x2, Jukebox.Var z2],
       f3 :@: [Jukebox.Var y2, Jukebox.Var z3]])
      | f1 == f2 && f2 == f3 && g1 == g2 &&
        x1 == x2 && y1 == y2 && z1 == z2 && z2 == z3 =
        Just (f1, g1, Jukebox.typ x1)
    checkDistributivity _ _ = Nothing

    define name t = do
      let vs  = Jukebox.vars t
          g = name ::: FunType (map typ vs) (typ t)
          c = clause [Pos (g :@: map Jukebox.Var vs Jukebox.:=: t)]
      return Input{ident = Nothing, tag = "distributivity_heuristic", kind = Jukebox.Ax Definition,
                   what = c, source = Unknown }

-- Encode existentials so that all goals are ground.
addNarrowing :: Bool -> TweeContext -> Problem Clause -> Problem Clause
addNarrowing alwaysNarrow TweeContext{..} prob =
  unchanged ++ equalityClauses
  where
    prob' = [inp { ident = Just (variant "addNarrowing" [i :: Int]) } | (i, inp) <- zip [0..] prob]

    (unchanged, nonGroundGoals) = partitionEithers (map f prob')
      where
        f inp@Input{what = Clause (Bind _ [Neg (x Jukebox.:=: y)])}
          | not (ground x) || not (ground y) || alwaysNarrow =
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
              ident = Just (name "addNarrowing2"),
              tag  = "new_negated_conjecture",
              kind = Jukebox.Ax NegatedConjecture,
              what =
                let form = And (map (Literal . snd) equalityLiterals) in
                ForAll (Bind (Set.fromList (vars form)) form),
              source =
                inference "encode_existential" "esa"
                  (map (fmap toForm . fst) nonGroundGoals) }

          input tag form i =
            Input {
              ident = Just (variant "addNarrowing3" [i :: Int]),
              tag = tag,
              kind = Jukebox.Ax NegatedConjecture,
              what = clause [form],
              source =
                inference "split_conjunct" "thm" [justification] }

        in [input tag form i | ((tag, form), i) <- zip equalityLiterals [0..]]

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

runTwee :: GlobalFlags -> TSTPFlags -> HornFlags -> [String] -> Config Constant -> CP.Config -> MainFlags -> (IO () -> IO ()) -> Problem Clause -> IO Answer
runTwee globals (TSTPFlags tstp) horn precedence config0 cpConfig flags@MainFlags{..} later obligs = {-# SCC runTwee #-} do
  let
    -- Encode whatever needs encoding in the problem
    obligs1
      | flags_flatten_goals_lightly = flattenGoals flags_flatten_backwards_goal flags_flatten_nonground False False obligs
      | flags_flatten_all = flattenGoals flags_flatten_backwards_goal flags_flatten_nonground True True obligs
      | flags_flatten_goals = flattenGoals flags_flatten_backwards_goal flags_flatten_nonground False True obligs
      | otherwise = obligs
    obligs2
      | flags_distributivity_heuristic = addDistributivityHeuristic obligs1
      | otherwise = obligs1
    ctx = makeContext obligs2
    lowercaseSkolem x
      | hasLabel "skolem" x =
        withRenamer x $ \s i ->
          case defaultRenamer s i of
            Renaming xss xs ->
              Renaming (map (map toLower) xss) (map toLower xs)
      | otherwise = x
    prob = prettyNames (mapName lowercaseSkolem (addNarrowing flags_equals_transformation ctx obligs2))

  (unsortedAxioms0, goals0) <-
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
        (Just c == maxUnary)
        (isNothing (elemIndex (base c) precedence))
        (fmap negate (elemIndex (base c) precedence))
        (maybeNegate (Map.findWithDefault 0 c funOccs))
    maybeNegate = if flags_flip_ordering then negate else id
    funOccs = funsOcc prob
    maxUnary =
      case filter (\(f, _) -> arity f == 1 && not (isType f)) (Map.toList funOccs) of
        [] -> Nothing
        xs -> Just (fst (maximumBy (comparing snd) xs))

    -- Translate everything to Twee.
    toEquation (t, u) =
      canonicalise (tweeTerm flags horn ctx prec t :=: tweeTerm flags horn ctx prec u)

    axiomCompare ax1 ax2
      | isEquality ax1' && not (isEquality ax2') = GT
      | isEquality ax2' && not (isEquality ax1') = LT
      | ax1' `simplerThan` ax2' = LT
      | ax2' `simplerThan` ax1' = GT
      | otherwise = EQ
      where
        ax1' = toEquation (pre_eqn ax1)
        ax2' = toEquation (pre_eqn ax2)
        isEquality ax = isJust (decodeEquality (eqn_lhs ax)) || isJust (decodeEquality (eqn_rhs ax))
    axioms0 = sortBy axiomCompare unsortedAxioms0

    goals =
      [ goal n pre_name (toEquation pre_eqn)
      | (n, PreEquation{..}) <- zip [1..] goals0 ]
    axioms =
      [ Axiom n pre_name (toEquation pre_eqn)
      | (n, PreEquation{..}) <- zip [1..] axioms0 ]
    defs =
      [ axiom
      | (axiom, PreEquation{..}) <- zip axioms axioms0,
        isDefinition pre_form ]
    isDefinition Input{source = Unknown} = True
    isDefinition inp = tag inp `elem` flags_eliminate

  -- Compute CP scoring heuristic
  let
    goalNests = nests (map goal_eqn goals)
    goalOccs = occs (map goal_eqn goals)
    score depth eqn
      | flags_goal_heuristic =
        fromIntegral (CP.score cpConfig depth eqn) *
        product
          [ pos (IntMap.findWithDefault 0 f eqnNests - IntMap.findWithDefault 0 f goalNests) *
            pos (IntMap.findWithDefault 0 f eqnOccs - IntMap.findWithDefault 0 f goalOccs)
          | f <- IntMap.keys eqnNests ] -- skip constants
      | otherwise = 
        fromIntegral (CP.score cpConfig depth eqn)
      where
        eqnNests = nests eqn
        eqnOccs = occs eqn

        pos :: Int -> Float
        pos n = if n <= 0 then 1 else fromIntegral n+1
    config = config0 { cfg_score_cp = score, cfg_eliminate_axioms = if flags_flatten_regeneralise then defs else [] }

  let
    withGoals = foldl' (addGoal config) (initialState config) goals
    withAxioms = foldl' (addAxiom config) withGoals axioms
    withBackwardsGoal = foldn rewriteGoalsBackwards withAxioms flags_backwards_goal

  -- Set up tracing.
  sayTrace <-
    case flags_trace of
      Nothing -> return $ \_ -> return ()
      Just (file, mod) -> do
        h <- openFile file WriteMode
        hSetBuffering h LineBuffering
        let put msg = hPutStrLn h msg
        put $ ":- module(" ++ mod ++ ", [step/1, lemma/1, axiom/1, goal/1])."
        put ":- discontiguous(step/1)."
        put ":- discontiguous(lemma/1)."
        put ":- discontiguous(axiom/1)."
        put ":- discontiguous(goal/1)."
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
    traceMsg (Status n) =
      step "status" [pPrint n]

    traceActive Active{active_top = Nothing, ..} =
      traceApp "rule" [pPrint active_id, traceEqn (unorient active_rule)]
    traceActive Active{active_top = Just top, ..} =
      traceApp "rule" [pPrint active_id, traceEqn (unorient active_rule), traceEqn lemma1, traceEqn lemma2]
      where
        (lemma1, lemma2) =
          find (steps (derivation active_proof))
        find (s1:s2:_)
          | eqn_rhs (equation (certify s1)) == top && eqn_lhs (equation (certify s2)) == top =
            (lemmaOf s1, lemmaOf s2)
        find (_:xs) = find xs
        lemmaOf s =
          case (usedLemmas s, usedAxioms s) of
            ([p], []) -> equation p
            ([], [ax]) -> axiom_eqn ax

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

  state <- complete output config withBackwardsGoal
  line

  when (solved state && flags_proof) $ later $ do
    let
      cfg_present
        | tstp && flags_formal_proof =
          (cfg_proof_presentation config){cfg_all_lemmas = True}
        | otherwise =
          cfg_proof_presentation config
      pres = present cfg_present $ map (eliminateDefinitionsFromGoal defs) $ solutions state

    sayTrace ""
    forM_ (pres_axioms pres) $ \p ->
      sayTrace $ show $
        traceApp "axiom" [traceEqn (axiom_eqn p)] <#> text "."
    forM_ (pres_lemmas pres) $ \p ->
      sayTrace $ show $
        traceApp "lemma" [traceEqn (equation p)] <#> text "."
    forM_ (pres_goals pres) $ \p ->
      sayTrace $ show $
        traceApp "goal" [traceEqn (pg_goal_hint p)] <#> text "."

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
            go Input{source = Inference _ _ inps} = concatMap (go . inputValue) inps
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
        (KBO.size (lhs rule), lhs rule,
         KBO.size (rhs rule), rhs rule)
      actives =
        sortBy (comparing (score . active_rule)) $
        IntMap.elems (st_active_set state')

    when (tstp && configIsComplete config) $ do
      putStrLn "% SZS output start Saturation"
      print $ pPrintProof $
        map pre_form axioms0 ++
        map pre_form goals0 ++
        [ Input Nothing "rule" (Jukebox.Ax Jukebox.Axiom) Unknown $
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
  (Jukebox.Term -> Jukebox.Term -> Equation Constant) ->
  -- Axioms, indexed by axiom number.
  [(Int, Input Form)] ->
  -- N.B. the formula here proves the negated goal.
  [(Int, Input Form)] ->
  Presentation Constant ->
  Problem Form
presentToJukebox ctx toEquation axioms goals Presentation{..} =
  [ Input {
      ident = Nothing,
      tag = pg_name,
      kind = Jukebox.Ax Jukebox.Axiom,
      what = false,
      source =
        inference "resolution" "thm"
          [-- A proof of t != u
           existentialHack pg_goal_hint (fromJust (lookup pg_number goals)),
           -- A proof of t = u
           fromJust (Map.lookup pg_number goal_proofs)] }
  | ProvedGoal{..} <- pres_goals ]

  where
    axiom_proofs =
      Map.fromList
        [ (axiom_number, (fromJust (lookup axiom_number axioms)) { ident = Just (ident axiom_number) })
        | Axiom{..} <- pres_axioms ]
      where
        ident i = variant "axiom" [i]

    lemma_proofs =
      Map.fromList [(p, (tstp p) { ident = Just (ident i) }) | (i, p) <- zip [0..] pres_lemmas]
      where
        ident i = variant "lemma" [i :: Int]

    goal_proofs =
      Map.fromList [(pg_number, tstp pg_proof) | ProvedGoal{..} <- pres_goals]

    tstp :: Proof Constant -> Input Form
    tstp = deriv . derivation

    deriv :: Derivation Constant -> Input Form
    deriv p =
      Input {
        ident = Nothing,
        tag = "step",
        kind = Jukebox.Ax Jukebox.Axiom,
        what = jukeboxEquation (equation (certify p)),
        source =
          inference name "thm" sources }
      where
        (name, sources) = unpack p

    unpack :: Derivation Constant -> (String, [Input Form])
    unpack (Refl _) = ("reflexivity", [])
    unpack (Symm p) = ("symmetry", [deriv p])
    unpack (Trans p q) = ("transitivity", [deriv p, deriv q])
    unpack (Cong _ ps) = ("congruence", [deriv p | p <- ps, let t :=: u = equation (certify p), t /= u])
    unpack (UseAxiom Axiom{..} _) =
      ("substitution", [fromJust (Map.lookup axiom_number axiom_proofs)])
    unpack (UseLemma lemma _) =
      ("substitution", [fromJust (Map.lookup lemma lemma_proofs)])

    jukeboxEquation :: Equation Constant -> Form
    jukeboxEquation (t :=: u) =
      toForm $ clause [Pos (jukeboxTerm ctx t Jukebox.:=: jukeboxTerm ctx u)]

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
            concatMap (find . inputValue) inps
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
  stampM (intern "twee") . join . parseCommandLineWithExtraArgs
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
             parseCPConfig <*>
             parseMainFlags <*>
             (toFormulasBox =>>=
              expert (toFof <$> clausifyBox <*> pure (tags True)) =>>=
              expert clausifyBox =>>= expert oneConjectureBox) <*>
             (runTwee <$> globalFlags <*> tstpFlags <*> expert hornFlags <*> parsePrecedence)))
  profile
  where
    combine horn config cpConfig main encode prove later prob0 = do
      res <- horn prob0
      case res of
        Left ans -> return ans
        Right prob -> do
          let
            isUnitEquality [Pos (_ Jukebox.:=: _)] = True
            isUnitEquality [Neg (_ Jukebox.:=: _)] = True
            isUnitEquality _ = False
            isUnit = all isUnitEquality (map (toLiterals . what) prob0)
            main' = if isUnit then main{flags_explain_encoding = False} else main{flags_formal_proof = False}
          encode prob >>= prove config cpConfig main' later
