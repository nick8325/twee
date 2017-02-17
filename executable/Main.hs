{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP, GeneralizedNewtypeDeriving, TypeFamilies, RecordWildCards, FlexibleContexts, UndecidableInstances, NondecreasingIndentation, OverloadedStrings, BangPatterns #-}
#include "errors.h"

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

import Control.Monad
import Data.Char
import Data.Either
import Twee hiding (message)
import Twee.Base hiding (char, lookup, (<>))
import Twee.Rule
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
import Jukebox.Form hiding ((:=:), Var, Symbolic(..), Term)
import Jukebox.Monotonox.ToFOF
import qualified Data.Set as Set

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
    conIndex :: Int,
    conArity :: Int,
    conSize  :: Int,
    conName  :: String }
  | Builtin Builtin

data Builtin = CFalse | CTrue | CEquals deriving (Eq, Ord)

instance Eq Constant where
  x == y = x `compare` y == EQ
instance Ord Constant where
  compare Constant{conIndex = x} Constant{conIndex = y} = compare x y
  compare Constant{} Builtin{} = LT
  compare Builtin{} Constant{} = GT
  compare (Builtin x) (Builtin y) = compare x y
instance Sized Constant where
  size Constant{conSize = n} = fromIntegral n
  size Builtin{} = 0
instance Arity Constant where
  arity Constant{conSize = n} = n
  arity (Builtin CEquals) = 2
  arity (Builtin _) = 0
instance Equals (Extended Constant) where
  equalsCon = fun (Function (Builtin CEquals))
  trueCon = fun (Function (Builtin CTrue))
  falseCon = fun (Function (Builtin CFalse))

instance Pretty Constant where
  pPrint Constant{conName = name} = text name
  pPrint (Builtin CEquals) = text "$equals"
  pPrint (Builtin CTrue) = text "$true"
  pPrint (Builtin CFalse) = text "$false"
instance PrettyTerm Constant where
  termStyle con@Constant{}
    | not (any isAlphaNum (conName con)) =
      case conArity con of
        1 -> prefix
        2 -> infixStyle 5
        _ -> uncurried
  termStyle _ = uncurried

instance Ordered (Extended Constant) where
  f << g = fun_value f < fun_value g
  lessEq t u = {-# SCC lessEq #-} KBO.lessEq t u
  lessIn model t u = {-# SCC lessIn #-} KBO.lessIn model t u

toTwee :: Problem Clause -> ([Equation Jukebox.Function], [Equation Jukebox.Function])
toTwee prob = partitionEithers (map eq prob)
  where
    eq Input{what = Clause (Bind _ [Pos (t Jukebox.:=: u)])} =
      Left (build (tm t) :=: build (tm u))
    eq Input{what = Clause (Bind _ [Neg (t Jukebox.:=: u)])} =
      Right (build (tm t) :=: build (tm u))
    eq _ = ERROR("Problem is not unit equality")

    tm (Jukebox.Var (Unique x _ _ ::: _)) =
      var (V (fromIntegral x))
    tm (f :@: ts) =
      app (fun f) (map tm ts)

addNarrowing ::
  ([Equation (Extended Constant)], [Equation (Extended Constant)]) ->
  ([Equation (Extended Constant)], [Equation (Extended Constant)])
addNarrowing (axioms, goals) =
    (axioms ++ concatMap encode nonground,
     ground ++ if null nonground && not (null goals) then [] else eqAxiom)
  where
    (ground, nonground) = partition isGround goals

    eqAxiom = [build (con falseCon) :=: build (con trueCon)]

    encode (t :=: u) =
      [build (app equalsCon [var (V 0), var (V 0)]) :=: build (con trueCon),
       build (app equalsCon [t, u]) :=: build (con falseCon)]

runTwee :: GlobalFlags -> Bool -> Config -> [String] -> Problem Clause -> IO Answer
runTwee globals tstp config precedence obligs = {-# SCC runTwee #-} do
  let line = unless (quiet globals) (putStrLn "")

  let (axioms0, goals0) = toTwee obligs
      prec c = (isNothing (elemIndex (base c) precedence),
                fmap negate (elemIndex (base c) precedence),
                negate (occ (fun c) (axioms0, goals0)))
      fs0 = map fun_value (usort (funs (axioms0, goals0)))
      fs1 = sortBy (comparing prec) fs0
      fs2 = zipWith (\i (c ::: (FunType args _)) -> Constant i (length args) 1 (show c)) [1..] fs1
      m  = Map.fromList (zip fs1 (map Function fs2))
  let replace = build . mapFun (fun . flip (Map.findWithDefault __) m . fun_value)
      axioms1 = map (bothSides replace) axioms0
      goals1  = map (bothSides replace) goals0
      (axioms2, goals2) = addNarrowing (axioms1, goals1)

  let
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
  state <-
    complete output config $
      foldl' (uncurry . addAxiom config)
        (foldl' (addGoal config) initialState goals2)
      (zip (repeat "axioms") axioms2)

  return $
    if solved state then Unsatisfiable else NoAnswer GaveUp

main = do
  let twee = Tool "twee" "twee - the Wonderful Equation Engine" "1" "Proves equations."
  join . parseCommandLine twee . tool twee $
    greetingBox twee =>>
    allFilesBox <*>
      (parseProblemBox =>>=
       (toFofIO <$> globalFlags <*> clausifyBox <*> pure (tags False)) =>>=
       clausifyBox =>>=
       allObligsBox <*>
         (runTwee <$> globalFlags <*> parseTSTP <*> parseConfig <*> parsePrecedence))
