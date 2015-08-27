-- Terms and evaluation.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances, DeriveFunctor, FlexibleContexts, GADTs #-}
module KBC.Term where

#include "errors.h"
import Data.List
import KBC.Base
#if __GLASGOW_HASKELL__ < 710
import KBC.Utils
#endif
import qualified Data.Map.Strict as Map
import qualified Data.Rewriting.Substitution.Type as Subst

class Minimal a where
  minimal :: a

minimalTerm :: Minimal f => Tm f
minimalTerm = Fun minimal []

class Skolem a where
  skolem  :: Int -> a

skolemConst :: Skolem f => Int -> Tm f
skolemConst n = Fun (skolem n) []

skolemise :: Skolem f => Tm f -> Tm f
skolemise = foldTerm (skolemConst . number) Fun

class (Ord f, PrettyTerm f, Minimal f, Numbered f, Skolem f, Arity f) => Function f

class Arity a where
  arity :: a -> Int

class Sized a where
  size  :: a -> Int

instance Sized f => Sized (Tm f) where
  size (Var _) = 1
  size (Fun f xs) = size f + sum (map size xs)

