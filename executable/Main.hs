{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP, GeneralizedNewtypeDeriving #-}
#include "errors.h"
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Char
import qualified Data.Map as Map
import KBC
import KBC.Base hiding (char)
import KBC.Term
import KBC.Equation
import KBC.Utils
import Data.Rewriting.Rule(Rule(..))
import Text.ParserCombinators.ReadP
import Data.List
import System.Environment
import Data.Ord

data Constant =
  Constant {
    conIndex :: Int,
    conArity :: Int,
    conSize  :: Int,
    conName  :: String }

con0 = Constant 0 0 1 "*"

instance Eq Constant where
  x == y = x `compare` y == EQ
instance Ord Constant where compare = comparing conIndex

instance Minimal Constant where
  minimal = con0
  
instance Sized Constant where
  funSize = fromIntegral . conSize
  funArity = conArity

instance Pretty Constant where pPrint = text . conName
instance PrettyTerm Constant

newtype Variable = V Int deriving (Eq, Ord, Numbered)

instance Pretty Variable where
  pPrint (V x) = text "X" <> pPrint x

parseDecl :: Int -> ReadP Constant
parseDecl n = do
  name <- munch1 (/= '/')
  char '/'
  size <- readS_to_P reads
  char '='
  arity <- readS_to_P reads
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
  return (t :==: u)

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

main = do
  [size] <- getArgs
  input  <- getContents
  let (sig, ("--":eqs1)) = break (== "--") (lines input)
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
  putStrLn "\nGo!"

  norm <-
    flip evalStateT (initialState (read size)) $ do
      mapM_ newEquation axioms
      complete
      normaliser

  putStrLn "\nHere we are:"
  forM_ goals $ \t ->
    prettyPrint (Rule t (norm t))
