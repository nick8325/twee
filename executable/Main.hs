{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, CPP, GeneralizedNewtypeDeriving, TypeFamilies #-}
#include "errors.h"

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

import Control.Monad
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Class
import Data.Char
import KBC
import KBC.Base hiding (char)
import KBC.Rule
import KBC.Utils
import KBC.Queue
import Data.Rewriting.Term(Term)
import Text.ParserCombinators.ReadP hiding (get)
import System.Environment
import System.Exit
import Data.Ord
import qualified KBC.Index as Index
import System.Exit
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import qualified KBC.KBO as KBO
import qualified Data.Set as Set

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
instance Numbered Constant where
  number = conIndex
  withNumber = __

instance Minimal Constant where
  minimal = con0
instance Skolem Constant where
  skolem n = Constant (-(n+1)) 0 1 ("sk" ++ show n)
  
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

instance Ordered Constant where
  lessEq = KBO.lessEq
  lessEqIn = KBO.lessEqIn

instance Function Constant

parseDecl :: Int -> StateT (Int, Map String Int) ReadP Constant
parseDecl n = lift $ do
  name <- munch1 (/= '/')
  char '/'
  arity <- readS_to_P reads
  char '='
  size <- readS_to_P reads
  return (Constant n arity size name)

parseTerm :: StateT (Int, Map String Int) ReadP (Tm String)
parseTerm = var `mplus` fun
  where
    fun = do
      x <- lift $ satisfy (\c -> c `notElem` "(),=_" && not (isUpper c))
      xs <- lift $ munch (\c -> c `notElem` "(),=")
      args <- args `mplus` return []
      return (Fun (x:xs) args)
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

    var = fmap (Var . MkVar) $ do
      x <- lift $ satisfy (\c -> isUpper c || c == '_')
      xs <- lift $ munch isAlphaNum
      let v = x:xs
      (k, m) <- get
      case Map.lookup v m of
        Just n -> return n
        Nothing -> do
          put (k+1, Map.insert v k m)
          return k

parseEquation :: StateT (Int, Map String Int) ReadP (Equation String)
parseEquation = do
  t <- parseTerm
  lift $ string "="
  u <- parseTerm
  return (t :=: u)

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

check :: (Symbolic a, ConstantOf a ~ Constant) => a -> IO ()
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
      axioms = map (bothSides (mapTerm (replace fs))) axioms1
      goals2 = map (mapTerm (replace fs)) goals1

  putStrLn "Axioms:"
  mapM_ prettyPrint axioms
  putStrLn "\nGoals:"
  mapM_ prettyPrint goals2
  check (axioms, goals2)
  putStrLn "\nGo!"

  let
    identical xs = not (Set.null (foldr1 Set.intersection xs))

    loop = do
      res <- complete1
      goals <- gets goals
      when (res && (length goals <= 1 || not (identical goals))) loop

    s =
      flip execState (initialState (read size) (map Set.singleton goals2)) $ do
        mapM_ newEquation axioms
        loop

    rs = map (critical . modelled . peel) (Index.elems (labelledRules s))

  putStrLn "\nFinal rules:"
  mapM_ prettyPrint rs
  putStrLn ""

  putStrLn (report s)

  unless (null goals2) $ do
    putStrLn "\nNormalised goal terms:"
    forM_ goals2 $ \t ->
      prettyPrint (Rule Oriented t (result (normalise s t)))

  if identical (goals s)
    then exitWith ExitSuccess
    else exitWith (ExitFailure 1)
