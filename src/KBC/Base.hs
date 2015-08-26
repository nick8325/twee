-- Imports the relevant parts of the term-rewriting package
-- and provides a few things on top.

{-# LANGUAGE TypeSynonymInstances, TypeFamilies, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving #-}
module KBC.Base(
  Var(..), Tm, TmOf, Subst, SubstOf, CPOf, RuleOf,
  module Data.Rewriting.Term, foldTerm, mapTerm,
  module Data.Rewriting.Term.Ops,
  module Data.Rewriting.Substitution, evalSubst, subst, matchMany, unifyMany,
  Symbolic(..), terms, varsDL, vars, funsDL, funs, symbolsDL, symbols,
  Numbered(..), canonicalise,
  module KBC.Pretty,
  module Text.PrettyPrint.HughesPJClass) where

import Control.Monad
import qualified Data.DList as DList
import Data.DList(DList)
import Data.List
import qualified Data.Map as Map
import qualified Data.Rewriting.CriticalPair as CP
import Data.Rewriting.Rule hiding (varsDL, funsDL, vars, funs)
import qualified Data.Rewriting.Substitution as T
import Data.Rewriting.Substitution hiding (apply, fromString, parse, parseIO, Subst)
import qualified Data.Rewriting.Substitution.Type as T
import qualified Data.Rewriting.Term as T
import Data.Rewriting.Term hiding (Term, fold, map, fromString, parse, parseIO, parseFun, parseVar, parseWST, vars, funs, varsDL, funsDL)
import Data.Rewriting.Term.Ops(subterms)
import KBC.Pretty
import Text.PrettyPrint.HughesPJClass hiding (empty)
import Data.Ord

-- A type of variables.
newtype Var = MkVar Int deriving (Eq, Ord, Show, Enum, Numbered)

instance Pretty Var where
  pPrint (MkVar x) = text "X" <> pPrint (x+1)

-- Renamings of functionality from term-rewriting.
type Tm f = T.Term f Var
type Subst f = T.Subst f Var

foldTerm :: (Var -> a) -> (f -> [a] -> a) -> Tm f -> a
foldTerm = T.fold

mapTerm :: (f -> f') -> Tm f -> Tm f'
mapTerm f = T.map f id

evalSubst :: Subst f -> Var -> Tm f
evalSubst s = subst s . Var

subst :: Subst f -> Tm f -> Tm f
subst = T.apply

matchMany :: Ord f => f -> [(Tm f, Tm f)] -> Maybe (Subst f)
matchMany def ts = match (Fun def (map fst ts)) (Fun def (map snd ts))

unifyMany :: Ord f => f -> [(Tm f, Tm f)] -> Maybe (Subst f)
unifyMany def ts = unify (Fun def (map fst ts)) (Fun def (map snd ts))

instance (Eq f, Eq v, Eq v') => Eq (GSubst v f v') where
  x == y = T.toMap x == T.toMap y
instance (Ord f, Ord v, Ord v') => Ord (GSubst v f v') where
  compare = comparing T.toMap
instance (PrettyTerm f, Pretty v, Pretty v') => Pretty (GSubst v f v') where
  pPrintPrec l p = pPrintPrec l p . T.toMap

-- Generalisation of term functionality to things that contain terms.
class Symbolic a where
  {-# MINIMAL (term|termsDL), substf #-}
  type ConstantOf a

  term :: a -> TmOf a
  term t = DList.head (termsDL t)

  termsDL :: a -> DList (TmOf a)
  termsDL t = return (term t)

  substf :: (Var -> TmOf a) -> a -> a

type TmOf a = Tm (ConstantOf a)
type SubstOf a = Subst (ConstantOf a)
type CPOf a = CP.CP (ConstantOf a) Var
type RuleOf a = Rule (ConstantOf a) Var

terms :: Symbolic a => a -> [TmOf a]
terms = DList.toList . termsDL

instance Symbolic (Tm f) where
  type ConstantOf (Tm f) = f
  substf sub = foldTerm sub Fun
  term = id

instance Symbolic (Rule f Var) where
  type ConstantOf (Rule f Var) = f
  termsDL (Rule l r) = return l `mplus` return r
  substf sub (Rule l r) = Rule (substf sub l) (substf sub r)

instance (ConstantOf a ~ ConstantOf b,
          Symbolic a, Symbolic b) => Symbolic (a, b) where
  type ConstantOf (a, b) = ConstantOf a
  termsDL (x, y) = termsDL x `mplus` termsDL y
  substf sub (x, y) = (substf sub x, substf sub y)

instance Symbolic a => Symbolic [a] where
  type ConstantOf [a] = ConstantOf a
  termsDL ts = msum (map termsDL ts)
  substf sub = map (substf sub)

vars :: Symbolic a => a -> [Var]
vars = DList.toList . varsDL

varsDL :: Symbolic a => a -> DList Var
varsDL t = termsDL t >>= aux
  where
    aux (Fun _ xs) = msum (map aux xs)
    aux (Var x)    = return x

funs :: Symbolic a => a -> [ConstantOf a]
funs = DList.toList . funsDL

funsDL :: Symbolic a => a -> DList (ConstantOf a)
funsDL t = termsDL t >>= aux
  where
    aux (Fun f xs) = return f `mplus` msum (map aux xs)
    aux (Var _)    = mzero

symbols :: Symbolic a => a -> [Either (ConstantOf a) Var]
symbols = DList.toList . symbolsDL

symbolsDL :: Symbolic a => a -> DList (Either (ConstantOf a) Var)
symbolsDL t = termsDL t >>= aux
  where
    aux (Fun f xs) = return (Left f) `mplus` msum (map aux xs)
    aux (Var x)    = return (Right x)

class Numbered a where
  withNumber :: Int -> a -> a
  number :: a -> Int

instance Numbered Int where
  withNumber = const
  number = id

instance (Numbered a, Numbered b) => Numbered (Either a b) where
  withNumber n (Left x)  = Left  (withNumber n x)
  withNumber n (Right x) = Right (withNumber n x)
  number = error "Can't take number of Either"

canonicalise :: Symbolic a => a -> a
canonicalise t = substf (evalSubst sub) t
  where
    sub = T.fromMap (Map.fromList (zipWith f vs [0..]))
    f x n = (x, Var (withNumber n x))
    vs  = vs' ++ (nub (concatMap vars (terms t)) \\ vs')
    vs' = nub (vars (term t))
