{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP, GeneralizedNewtypeDeriving, TypeFamilies, RecordWildCards, FlexibleContexts, UndecidableInstances, NondecreasingIndentation #-}
#include "errors.h"

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

import Control.Monad
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Data.Char
import Twee hiding (info)
import Twee.Base hiding (char, lookup, (<>), replace)
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
import qualified Twee.LPO as LPO
import qualified Data.Set as Set
import Data.Reflection
import Data.Array
import Options.Applicative
import qualified Data.IntMap as IntMap
import Data.IntMap(IntMap)

parseInitialState :: Parser (Twee f)
parseInitialState =
  go <$> maxSize <*> inversion <*> skolem <*> ground <*> general
     <*> overgeneral <*> groundJoin <*> conn <*> set <*> setGoals <*> tracing <*> moreTracing <*> weight <*> splits <*> cpSetSize <*> mixFIFO <*> mixPrio
  where
    go maxSize inversion skolem ground general overgeneral groundJoin conn set setGoals tracing moreTracing weight splits cpSetSize mixFIFO mixPrio =
      (initialState mixFIFO mixPrio) {
        maxSize = maxSize,
        cpSplits = splits,
        minimumCPSetSize = cpSetSize,
        useInversionRules = inversion,
        useSkolemPenalty = skolem,
        useGroundPenalty = ground,
        useGeneralSuperpositions = general,
        useOvergeneralSuperpositions = overgeneral,
        useGroundJoining = groundJoin,
        useConnectedness = conn,
        useSetJoining = set,
        useSetJoiningForGoals = setGoals,
        tracing = tracing,
        moreTracing = moreTracing,
        lhsWeight = weight }
    maxSize = (Just <$> option auto (long "max-size" <> help "Maximum critical pair size" <> metavar "SIZE")) <|> pure Nothing
    inversion = switch (long "inversion" <> help "Detect inversion rules")
    skolem = switch (long "skolem-penalty" <> help "Penalise critical pairs whose Skolemisation is joinable")
    ground = switch (long "ground-penalty" <> help "Penalise ground critical pairs")
    general = not <$> switch (long "no-general-superpositions" <> help "Disable considering only general superpositions")
    overgeneral = switch (long "overgeneral-superpositions" <> help "A more aggressive, incomplete version of --general-superpositions")
    groundJoin = not <$> switch (long "no-ground-join" <> help "Disable ground joinability testing")
    conn = not <$> switch (long "no-connectedness" <> help "Disable connectedness testing")
    set = switch (long "set-join" <> help "Join by computing set of normal forms")
    setGoals = not <$> switch (long "no-set-join-goals" <> help "Disable joining goals by computing set of normal forms")
    tracing = not <$> switch (long "no-tracing" <> help "Disable tracing output")
    moreTracing = switch (long "more-tracing" <> help "Produce even more tracing output")
    weight = option auto (long "lhs-weight" <> help "Weight given to LHS of critical pair (default 2)" <> value 2 <> metavar "WEIGHT")
    splits = option auto (long "split" <> help "Split CP sets into this many pieces on selection (default 20)" <> value 20)
    cpSetSize = option auto (long "cp-set-minimum" <> help "Decay CP sets into single CPs when they get this small (default 20)" <> value 20)
    mixFIFO = option auto (long "mix-fifo" <> help "Take this many CPs at a time from FIFO (default 0)" <> value 0)
    mixPrio = option auto (long "mix-prio" <> help "Take this many CPs at a time from priority queue (default 10)" <> value 10)

parseFile :: Parser String
parseFile = strArgument (metavar "FILENAME")

data Order = KBO | LPO

parseOrder :: Parser Order
parseOrder =
  flag' KBO (long "kbo" <> help "Use Knuth-Bendix ordering (default)") <|>
  flag' LPO (long "lpo" <> help "Use lexicographic path ordering") <|>
  pure KBO

data Constant =
  Constant {
    conIndex :: Int,
    conArity :: Int,
    conSize  :: Int,
    conName  :: String }

instance Eq Constant where
  x == y = x `compare` y == EQ
instance Ord Constant where
  compare = comparing conIndex
instance Sized Constant where
  size = fromIntegral . conSize
instance Arity Constant where
  arity = conArity

instance Pretty Constant where pPrint = text . conName
instance PrettyTerm Constant where
  termStyle con
    | not (any isAlphaNum (conName con)) =
      case conArity con of
        1 -> prefix
        2 -> infixStyle 5
        _ -> uncurried
  termStyle _ = uncurried

instance Given (IntMap Constant) => Numbered Constant where
  fromInt n = IntMap.findWithDefault __ n given
  toInt = conIndex

instance (Given Order, Given (IntMap Constant)) => Ordered (Extended Constant) where
  lessEq =
    case given of
      KBO -> KBO.lessEq
      LPO -> LPO.lessEq
  lessIn =
    case given of
      KBO -> KBO.lessIn
      LPO -> LPO.lessIn

parseDecl :: Int -> StateT (Int, Map String Int) ReadP Constant
parseDecl n = lift $ do
  name <- munch1 (/= '/')
  char '/'
  arity <- readS_to_P reads
  char '='
  size <- readS_to_P reads
  return (Constant n arity size name)

data Tm = AppTm String [Tm] | VarTm Var

parseTerm :: StateT (Int, Map String Int) ReadP Tm
parseTerm = var `mplus` fun
  where
    fun = do
      x <- lift $ satisfy (\c -> c `notElem` "(),=_" && not (isUpper c))
      xs <- lift $ munch (\c -> c `notElem` "(),=")
      args <- args `mplus` return []
      return (AppTm (x:xs) args)
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

check :: Given (IntMap Constant) => Term (Extended Constant) -> IO ()
check t = do
  forM_ (subterms t) $ \t ->
    case t of
      Fun f xs | arity f /= length (fromTermList xs) -> do
          print $
            fsep [
            text "Function",
            nest 2 (pPrint f),
            text "has arity",
            nest 2 (pPrint (arity f)),
            text "but called as",
            nest 2 (pPrint t)]
          exitWith (ExitFailure 1)
      _ -> return ()

main = do
  (state, file, order) <-
    execParser $
      info (helper <*> ((,,) <$> parseInitialState <*> parseFile <*> parseOrder))
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
      m  = IntMap.fromList [(conIndex f, f) | f <- fs0]
  give m $ give order $ do
  let fs = [(conName f, toFun (Function f)) | f <- fs0]

      translate (VarTm x) = build (var x)
      translate (AppTm f ts) = build (fun (replace fs f) (map translate ts))

      axioms1 = map (run parseEquation) (map tok axioms0)
      goals1 = map (run parseTerm . tok) goals0
      axioms = [translate t :=: translate u | (t, u) <- axioms1]
      goals2 = map translate goals1

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
