{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP, GeneralizedNewtypeDeriving, TypeFamilies #-}
#include "errors.h"

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Char
import KBC
import KBC.Base hiding (char)
import KBC.Term
import KBC.Equation
import KBC.Utils
import KBC.Rewrite
import KBC.Queue
import Data.Rewriting.Rule(Rule(..))
import Text.ParserCombinators.ReadP hiding (get)
import System.Environment
import System.Exit
import Data.Ord
import qualified KBC.Index as Index

data Constant =
  Constant {
    conIndex :: Int,
    conArity :: Int,
    conSize  :: Int,
    conName  :: String }

con0 = Constant 0 0 1 "?"

instance Eq Constant where
  x == y = x `compare` y == EQ
instance Ord Constant where compare = comparing conIndex
instance Numbered Constant where
  number = conIndex
  withNumber = __

instance Minimal Constant where
  minimal = con0
  
instance Sized Constant where
  funSize = fromIntegral . conSize
  funArity = conArity

instance Pretty Constant where pPrint = text . conName
instance PrettyTerm Constant where
  termStyle con
    | not (any isAlphaNum (conName con)) =
      case conArity con of
        1 -> prefix
        2 -> infixStyle 5
        _ -> uncurried
  termStyle _ = uncurried

newtype Variable = V Int deriving (Eq, Ord, Numbered)

instance Pretty Variable where
  pPrint (V x) = text "X" <> pPrint x

parseDecl :: Int -> ReadP Constant
parseDecl n = do
  name <- munch1 (/= '/')
  char '/'
  arity <- readS_to_P reads
  char '='
  size <- readS_to_P reads
  return (Constant n arity size name)

parseTerm :: ReadP (Tm String String)
parseTerm = var <++ fun
  where
    fun = do
      name <- munch1 (\c -> c `notElem` "(),")
      args <- args <++ return []
      return (Fun name args)
    args = between (char '(') (char ')') (sepBy parseTerm (char ','))

    var = fmap Var $ do
      x <- satisfy isUpper
      xs <- munch isAlphaNum
      return (x:xs)

parseEquation :: ReadP (Equation String String)
parseEquation = do
  t <- parseTerm
  string "="
  u <- parseTerm
  return (t :=: u)

run :: ReadP a -> String -> a
run p xs =
  case readP_to_S (p <* eof) xs of
    ((y, ""):_) -> y
    _ -> error "parse error"

tok :: String -> String
tok = filter (not . isSpace)

replace :: (Eq a, Show a) => [(a, b)] -> a -> b
replace xs x =
  case lookup x xs of
    Just y -> y
    Nothing -> error (show x ++ " not found")

check :: (Symbolic a, ConstantOf a ~ Constant, VariableOf a ~ Variable) => a -> IO ()
check eq = do
  forM_ (terms eq >>= subterms) $ \t ->
    case t of
      Fun f xs | conArity f /= length xs -> do
          print $
            fsep [
            text "Function",
            nest 2 (pPrint f),
            text "has arity",
            nest 2 (pPrint (conArity f)),
            text "but called as",
            nest 2 (pPrint (Fun f xs))]
          exitWith (ExitFailure 1)
      _ -> return ()

main = do
  [size] <- getArgs
  input  <- getContents
  let (sig, ("--":eqs1)) = break (== "--") (filter (not . comment) (lines input))
      comment ('%':_) = True
      comment _ = False
      (axioms0, ("--":goals0)) = break (== "--") eqs1
      fs0 = zipWith (run . parseDecl) [1..] (map tok sig)
      fs = [(conName f, f) | f <- fs0]
      axioms1 = map (run parseEquation) (map tok axioms0)
      goals1 = map (run parseTerm . tok) goals0
      vs = zip (usort (vars (axioms1, goals1))) (map V [0..])
      axioms = map (bothSides (mapTerm (replace fs) (replace vs))) axioms1
      goals = map (mapTerm (replace fs) (replace vs)) goals1

  putStrLn "Axioms:"
  mapM_ prettyPrint axioms
  putStrLn "\nGoals:"
  mapM_ prettyPrint goals
  check (axioms, goals)
  putStrLn "\nGo!"

  let
    stop
      | length goals <= 1 = return False
      | otherwise = do
          s <- get
          let goals' = map (result . normalise s) goals
          return (and (zipWith (==) goals' (tail goals')))

    loop = do
      res1 <- complete1
      res2 <- stop
      when (res1 && not res2) loop

    s =
      flip execState (initialState (read size)) $ do
        mapM_ newEquation axioms
        loop

    rs = map peel (Index.elems (labelledRules s))

  putStrLn "\nFinal rules:"
  mapM_ prettyPrint rs
  putStrLn ""

  putStrLn (report s)

  unless (null goals) $ do
    putStrLn "\nNormalised goal terms:"
    forM_ goals $ \t ->
      prettyPrint (Rule t (result (normalise s t)))
