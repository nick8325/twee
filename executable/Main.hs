{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP, GeneralizedNewtypeDeriving, TypeFamilies, RecordWildCards, FlexibleContexts, UndecidableInstances #-}
#include "errors.h"

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

import Control.Monad
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Data.Char
import Twee hiding (info)
import Twee.Base hiding (char, lookup, (<>))
import Twee.Rule
import Twee.Utils
import Twee.Queue
import Text.ParserCombinators.ReadP hiding (get, option)
import System.Environment
import System.Exit
import Data.Ord
import qualified Twee.Indexes as Indexes
import System.Exit
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import qualified Twee.KBO as KBO
import qualified Data.Set as Set
import Data.Reflection
import Data.Array
import Options.Applicative

parseInitialState :: Parser (Twee f)
parseInitialState =
  go <$> maxSize <*> inversion <*> skolem <*> ground <*> general
     <*> overgeneral <*> groundJoin <*> conn <*> set <*> weight
  where
    go maxSize inversion skolem ground general overgeneral groundJoin conn set weight =
      initialState {
        maxSize = maxSize,
        useInversionRules = inversion,
        useSkolemPenalty = skolem,
        useGroundPenalty = ground,
        useGeneralSuperpositions = general,
        useOvergeneralSuperpositions = overgeneral,
        useGroundJoining = groundJoin,
        useConnectedness = conn,
        useSetJoining = set,
        lhsWeight = weight }
    maxSize = (Just <$> option auto (long "max-size" <> help "Maximum critical pair size" <> metavar "SIZE")) <|> pure Nothing
    inversion = switch (long "inversion" <> help "Detect inversion rules")
    skolem = switch (long "skolem-penalty" <> help "Penalise critical pairs whose Skolemisation is joinable")
    ground = switch (long "ground-penalty" <> help "Penalise ground critical pairs")
    general = not <$> switch (long "no-general-superpositions" <> help "Disable considering only general superpositions")
    overgeneral = not <$> switch (long "no-overgeneral-superpositions" <> help "A more aggressive, incomplete version of --general-superpositions")
    groundJoin = not <$> switch (long "no-ground-join" <> help "Disable ground joinability testing")
    conn = not <$> switch (long "no-connectedness" <> help "Disable connectedness testing")
    set = not <$> switch (long "no-set-join" <> help "Disable joining by computing set of normal forms")
    weight = option auto (long "lhs-weight" <> help "Weight given to LHS of critical pair (default 2)" <> value 2 <> metavar "WEIGHT")

parseFile :: Parser String
parseFile = strArgument (metavar "FILENAME")

data Constant =
  Constant {
    conIndex :: Int,
    conArity :: Int,
    conSize  :: Int,
    conName  :: String }

con0 = Constant 0 0 1 "?"

instance Eq Constant where
  x == y = x `compare` y == EQ
instance Ord Constant where
  -- Skolem constants are smallest, except for minimal constant.
  compare = comparing (\c -> (conIndex c > 0, abs (conIndex c)))
{-instance Numbered Constant where
  number = conIndex
  withNumber = __-}

toFun :: Constant -> Fun Constant
toFun Constant{..}
  | conIndex >= 0 = MkFun (conIndex*2)
  | otherwise     = MkFun (negate conIndex*2-1)

newtype Context = Context (Array Int Constant)

fromFun :: Given Context => Fun Constant -> Constant
fromFun (MkFun n)
  | even n    = arr ! (n `div` 2)
  | otherwise = skolemFun (negate n `div` 2)
  where
    Context arr = given

instance Minimal Constant where
  minimal = toFun con0
instance Skolem Constant where
  skolem (MkVar n) = toFun (skolemFun n)

skolemFun n =  Constant (-(n+1)) 0 1 ("sk" ++ show n)

instance Given Context => Sized (Fun Constant) where
  size = fromIntegral . conSize . fromFun
instance Given Context => SizedFun Constant
instance Given Context => Arity Constant where
  arity = conArity . fromFun

instance Pretty Constant where pPrint = text . conName
instance Given Context => Pretty (Fun Constant) where
  pPrint = pPrint . fromFun
instance Given Context => PrettyTerm Constant where
  termStyle con0
    | not (any isAlphaNum (conName con)) =
      case conArity con of
        1 -> prefix
        2 -> infixStyle 5
        _ -> uncurried
    where
      con = fromFun con0
  termStyle _ = uncurried

instance Given Context => Ordered Constant where
  lessEq = KBO.lessEq
  lessIn = KBO.lessIn

instance Given Context => OrdFun Constant where
  compareFun = comparing fromFun
instance Given Context => Function Constant

parseDecl :: Int -> StateT (Int, Map String Int) ReadP Constant
parseDecl n = lift $ do
  name <- munch1 (/= '/')
  char '/'
  arity <- readS_to_P reads
  char '='
  size <- readS_to_P reads
  return (Constant n arity size name)

data Tm = App String [Tm] | VarTm Var

parseTerm :: StateT (Int, Map String Int) ReadP Tm
parseTerm = var `mplus` fun
  where
    fun = do
      x <- lift $ satisfy (\c -> c `notElem` "(),=_" && not (isUpper c))
      xs <- lift $ munch (\c -> c `notElem` "(),=")
      args <- args `mplus` return []
      return (App (x:xs) args)
    args = between (char '(') (char ')') (sepBy parseTerm (char ','))
    between p q r = do
      lift p
      x <- r
      lift q
      return x
    sepBy p q = do
      x  <- p
      xs <- (lift q >> sepBy p q) `mplus` return []
      return (x:xs)

    var = fmap (VarTm . MkVar) $ do
      x <- lift $ satisfy (\c -> isUpper c || c == '_')
      xs <- lift $ munch isAlphaNum
      let v = x:xs
      (k, m) <- get
      case Map.lookup v m of
        Just n -> return n
        Nothing -> do
          put (k+1, Map.insert v k m)
          return k

parseEquation :: StateT (Int, Map String Int) ReadP (Tm, Tm)
parseEquation = do
  t <- parseTerm
  lift $ string "="
  u <- parseTerm
  return (t, u)

run :: StateT (Int, Map String Int) ReadP a -> String -> a
run p xs =
  case readP_to_S (evalStateT p (0, Map.empty) <* eof) xs of
    ((y, ""):_) -> y
    _ -> error "parse error"

tok :: String -> String
tok = filter (not . isSpace)

replace :: (Eq a, Show a) => [(a, b)] -> a -> b
replace xs x =
  case lookup x xs of
    Just y -> y
    Nothing -> error (show x ++ " not found")

check :: Given Context => Term Constant -> IO ()
check t = do
  forM_ (subterms t) $ \t ->
    case t of
      Fun f xs | conArity (fromFun f) /= length (fromTermList xs) -> do
          print $
            fsep [
            text "Function",
            nest 2 (pPrint f),
            text "has arity",
            nest 2 (pPrint (conArity (fromFun f))),
            text "but called as",
            nest 2 (pPrint t)]
          exitWith (ExitFailure 1)
      _ -> return ()

main = do
  (state, file) <-
    execParser $
      info (helper <*> ((,) <$> parseInitialState <*> parseFile))
        (fullDesc <>
         header "twee - an equational theorem prover")
  input <-
    case file of
      "-" -> getContents
      _ -> readFile file
  let (sig, ("--":eqs1)) = break (== "--") (filter (not . comment) (lines input))
      comment ('%':_) = True
      comment _ = False
      (axioms0, ("--":goals0)) = break (== "--") eqs1
      fs0 = zipWith (run . parseDecl) [1..] (map tok sig)
      fs1 = con0:fs0
      fs = [(conName f, toFun f) | f <- fs0]
      context =
        Context $
        array (0, maximum (map conIndex fs1))
          [(conIndex f, f) | f <- fs1]

      translate (VarTm x) = var x
      translate (App f ts) = fun (replace fs f) (map translate ts)

      axioms1 = map (run parseEquation) (map tok axioms0)
      goals1 = map (run parseTerm . tok) goals0
      axioms = [translate t :=: translate u | (t, u) <- axioms1]
      goals2 = map translate goals1

  give context $ do
    putStrLn "Axioms:"
    mapM_ prettyPrint axioms
    putStrLn "\nGoals:"
    mapM_ prettyPrint goals2
    mapM_ check goals2
    forM_ axioms $ \(t :=: u) -> do { check t; check u }
    putStrLn "\nGo!"

    let
      identical xs = not (Set.null (foldr1 Set.intersection xs))

      loop = do
        res <- complete1
        goals <- gets goals
        when (res && (length goals <= 1 || not (identical goals))) loop

      s =
        flip execState (addGoals (map Set.singleton goals2) state) $ do
          mapM_ newEquation axioms
          loop

      rs = map (critical . modelled . peel) (Indexes.elems (labelledRules s))

    putStrLn "\nFinal rules:"
    mapM_ prettyPrint rs
    putStrLn ""

    putStrLn (report s)

    unless (null goals2) $ do
      putStrLn "Normalised goal terms:"
      forM_ goals2 $ \t ->
        prettyPrint (Rule Oriented t (result (normalise s t)))

    if length (goals s) <= 1 || identical (goals s)
      then exitWith ExitSuccess
      else exitWith (ExitFailure 1)
