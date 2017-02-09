{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP, GeneralizedNewtypeDeriving, TypeFamilies, RecordWildCards, FlexibleContexts, UndecidableInstances, NondecreasingIndentation, OverloadedStrings #-}
#include "errors.h"

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

import Control.Monad
import Data.Char
import Data.Either
import Twee
import Twee.Base hiding (char, lookup, (<>))
import Twee.Rule
import Twee.Utils
import qualified Twee.CP as CP
import Data.Ord
import qualified Data.Map.Strict as Map
import qualified Twee.KBO as KBO
import qualified Twee.Index as Index
import Twee.Profile
import Data.List.Split
import Data.List
import Data.Maybe
import Jukebox.Options
import Jukebox.Toolbox
import Jukebox.Name
import qualified Jukebox.Form as Jukebox
import Jukebox.Form hiding ((:=:), Var, Symbolic(..), Term)
import Jukebox.Monotonox.ToFOF
import Control.Exception

parseConfig :: OptionParser Config
parseConfig =
  Config <$> maxSize <*> (CP.Config <$> lweight <*> rweight <*> funweight) <*> cpSetSize <*> splits
  where
    maxSize = flag "max-term-size" ["Maximum term size"] Nothing (Just <$> argNum)
    lweight = defaultFlag "lhs-weight" ["Weight given to LHS of critical pair"] (CP.cfg_lhsweight . cfg_critical_pairs) argNum
    rweight = defaultFlag "rhs-weight" ["Weight given to RHS of critical pair"] (CP.cfg_rhsweight . cfg_critical_pairs) argNum
    funweight = defaultFlag "fun-weight" ["Weight given to function symbols"] (CP.cfg_funweight . cfg_critical_pairs) argNum
    cpSetSize = defaultFlag "split-cp-set-at" ["Split CP sets into single CPs when they get this small"] cfg_split_cp_set_at argNum
    splits = defaultFlag "split-cp-set-into" ["Split CP sets into this many pieces on selection"] cfg_split_cp_set_into argNum

    defaultFlag name desc field parser =
      flag name (desc ++ ["Default value: " ++ show def]) def parser
      where
        def = field defaultConfig

parsePrecedence :: OptionParser [String]
parsePrecedence =
  fmap (splitOn ",")
  (flag "precedence" ["List of functions in descending order of precedence"] [] (arg "<function>" "expected a function name" Just))

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
  lessEq t u = stamp "KBO" (KBO.lessEq t u)
  lessIn model t u = stamp "KBO in model" (KBO.lessIn model t u)

toTwee :: Problem Clause -> ([Equation Jukebox.Function], [Term Jukebox.Function])
toTwee prob = (lefts eqs, goals)
  where
    eq Input{what = Clause (Bind _ [Pos (t Jukebox.:=: u)])} =
      Left (build (tm t) :=: build (tm u))
    eq Input{what = Clause (Bind _ [Neg (t Jukebox.:=: u)])} =
      Right (build (tm t) :=: build (tm u))
    eq _ = ERROR("Problem is not unit equality")

    eqs = map eq prob

    goals =
      case rights eqs of
        [] -> []
        [t :=: u] -> [t, u]
        _ -> ERROR("Problem is not unit equality")

    tm (Jukebox.Var (Unique x _ _ ::: _)) =
      var (V (fromIntegral x))
    tm (f :@: ts) =
      app (fun f) (map tm ts)

addNarrowing ::
  ([Equation (Extended Constant)], [Term (Extended Constant)]) ->
  ([Equation (Extended Constant)], [Term (Extended Constant)])
addNarrowing (axioms, goals)
  | length goals < 2 = (axioms, map build [con false, con true])
    where
      false  = fun (Function (Builtin CFalse))
      true   = fun (Function (Builtin CTrue))
addNarrowing (axioms, goals)
  | length goals >= 2 && all isGround goals = (axioms, goals)
addNarrowing (axioms, [t, u])
  | otherwise = (axioms ++ equalities, map build [con false, con true])
    where
      false  = fun (Function (Builtin CFalse))
      true   = fun (Function (Builtin CTrue))
      equals = fun (Function (Builtin CEquals))

      equalities =
        [build (app equals [var (V 0), var (V 0)]) :=: build (con true),
         build (app equals [t, u]) :=: build (con false)]
addNarrowing _ =
  ERROR("Don't know how to handle several non-ground goals")

runTwee :: Config -> [String] -> Problem Clause -> IO Answer
runTwee config precedence obligs = stampM "twee" $ do
  let (axioms0, goals0) = toTwee obligs
      prec c = (isNothing (elemIndex (base c) precedence),
                fmap negate (elemIndex (base c) precedence),
                negate (occ (fun c) (axioms0, goals0)))
      fs0 = map fun_value (usort (funs (axioms0, goals0)))
      fs1 = sortBy (comparing prec) fs0
      fs2 = zipWith (\i (c ::: (FunType args _)) -> Constant i (length args) 1 (show c)) [1..] fs1
      m  = Map.fromList (zip fs1 (map Function fs2))
  let replace = build . mapFun (fun . flip (Map.findWithDefault __) m . fun_value)
      axioms1 = [replace t :=: replace u | t :=: u <- axioms0]
      goals1  = map replace goals0
      (axioms2, goals2) = addNarrowing (axioms1, goals1)

  putStrLn "Axioms:"
  mapM_ prettyPrint axioms2
  putStrLn "\nGoals:"
  mapM_ prettyPrint goals2
  putStrLn "\nGo!"

  let
    state =
      complete config $
      foldl' (newEquation config) initialState { st_goals = goals2 } axioms2

  let rs = map rule_rule (Index.elems (st_rules state))

  putStrLn "Normalised goal terms:"
  forM_ goals2 $ \t ->
    prettyPrint (Rule Oriented t (result (normaliseWith (rewrite reduces (st_rules state)) t)))

  return $
    case () of
      _ | solved state -> Unsatisfiable
        | isJust (cfg_max_term_size config) -> NoAnswer GaveUp
        | otherwise -> NoAnswer GaveUp -- don't trust completeness

main = flip finally profile $ do
  let twee = Tool "twee" "twee - the Wonderful Equation Engine" "1" "Proves equations."
  join . parseCommandLine twee . tool twee $
    greetingBox twee =>>
    allFilesBox <*>
      (parseProblemBox =>>=
       (toFofIO <$> globalFlags <*> clausifyBox <*> pure (tags False)) =>>=
       clausifyBox =>>=
       allObligsBox <*>
         (runTwee <$> parseConfig <*> parsePrecedence))
