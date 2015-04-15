-- Imports the relevant parts of the term-rewriting package
-- and provides a few things on top.

{-# LANGUAGE CPP, TypeSynonymInstances, TypeFamilies, FlexibleContexts #-}
module KBC.Base(
  Tm, TmOf, SubstOf, CPOf, RuleOf,
  module Data.Rewriting.Term, foldTerm, mapTerm,
  module Data.Rewriting.Term.Ops,
  module Data.Rewriting.Substitution, evalSubst, subst, unifyMany,
  Symbolic(..), terms, varsDL, vars, funsDL, funs, symbolsDL, symbols,
  Numbered(..), canonicalise,
  module KBC.Pretty,
  module Text.PrettyPrint.HughesPJClass,
  PrettyTerm(..), TermStyle(..), pPrintStyle) where

#include "errors.h"
import Control.Monad
import qualified Data.DList as DList
import Data.DList(DList)
import Data.List
import qualified Data.Map as Map
import qualified Data.Rewriting.CriticalPair as CP
import Data.Rewriting.Rule hiding (varsDL, funsDL, vars, funs)
import qualified Data.Rewriting.Substitution as T
import Data.Rewriting.Substitution hiding (apply, fromString, parse, parseIO)
import qualified Data.Rewriting.Substitution.Type as T
import qualified Data.Rewriting.Term as T
import Data.Rewriting.Term hiding (Term, fold, map, fromString, parse, parseIO, parseFun, parseVar, parseWST, vars, funs, varsDL, funsDL)
import Data.Rewriting.Term.Ops(subterms)
import KBC.Pretty
import KBC.Utils
import Text.PrettyPrint.HughesPJClass hiding (empty)
import Data.Ord

-- Renamings of functionality from term-rewriting.
type Tm = T.Term

foldTerm :: (v -> a) -> (f -> [a] -> a) -> Tm f v -> a
foldTerm = T.fold

mapTerm :: (f -> f') -> (v -> v') -> Tm f v -> Tm f' v'
mapTerm = T.map

evalSubst :: Ord v => Subst f v -> v -> Tm f v
evalSubst s = subst s . Var

subst :: Ord v => Subst f v -> Tm f v -> Tm f v
subst = T.apply

unifyMany :: (Ord f, Ord v) => f -> [(Tm f v, Tm f v)] -> Maybe (Subst f v)
unifyMany def ts = unify (Fun def (map fst ts)) (Fun def (map snd ts))

instance (Eq f, Eq v, Eq v') => Eq (GSubst v f v') where
  x == y = T.toMap x == T.toMap y
instance (Ord f, Ord v, Ord v') => Ord (GSubst v f v') where
  compare = comparing T.toMap

-- Generalisation of term functionality to things that contain terms.
class Symbolic a where
  {-# MINIMAL (term|termsDL), substf #-}
  type ConstantOf a
  type VariableOf a

  term :: a -> TmOf a
  term t = DList.head (termsDL t)

  termsDL :: a -> DList (TmOf a)
  termsDL t = return (term t)

  substf :: (VariableOf a -> TmOf a) -> a -> a

type TmOf a = Tm (ConstantOf a) (VariableOf a)
type SubstOf a = Subst (ConstantOf a) (VariableOf a)
type CPOf a = CP.CP (ConstantOf a) (VariableOf a)
type RuleOf a = Rule (ConstantOf a) (VariableOf a)

terms :: Symbolic a => a -> [TmOf a]
terms = DList.toList . termsDL

instance Symbolic (Tm f v) where
  type ConstantOf (Tm f v) = f
  type VariableOf (Tm f v) = v
  substf sub = foldTerm sub Fun
  term = id

instance Symbolic (Rule f v) where
  type ConstantOf (Rule f v) = f
  type VariableOf (Rule f v) = v
  termsDL (Rule l r) = return l `mplus` return r
  substf sub (Rule l r) = Rule (substf sub l) (substf sub r)

instance (ConstantOf a ~ ConstantOf b,
          VariableOf a ~ VariableOf b,
          Symbolic a, Symbolic b) => Symbolic (a, b) where
  type ConstantOf (a, b) = ConstantOf a
  type VariableOf (a, b) = VariableOf a
  termsDL (x, y) = termsDL x `mplus` termsDL y
  substf sub (x, y) = (substf sub x, substf sub y)

instance Symbolic a => Symbolic [a] where
  type ConstantOf [a] = ConstantOf a
  type VariableOf [a] = VariableOf a
  termsDL ts = msum (map termsDL ts)
  substf sub = map (substf sub)

vars :: Symbolic a => a -> [VariableOf a]
vars = DList.toList . varsDL

varsDL :: Symbolic a => a -> DList (VariableOf a)
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

symbols :: Symbolic a => a -> [Either (ConstantOf a) (VariableOf a)]
symbols = DList.toList . symbolsDL

symbolsDL :: Symbolic a => a -> DList (Either (ConstantOf a) (VariableOf a))
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

canonicalise :: (Ord (VariableOf a), Numbered (VariableOf a), Symbolic a) => a -> a
canonicalise t = substf (evalSubst sub) t
  where
    sub = T.fromMap (Map.fromList (zipWith f vs [0..]))
    f x n = (x, Var (withNumber n x))
    vs  = vs' ++ (nub (concatMap vars (terms t)) \\ vs')
    vs' = nub (vars (term t))

class Pretty a => PrettyTerm a where
  termStyle :: a -> TermStyle
  termStyle _ = Curried

data TermStyle = Invisible | Curried | Uncurried | Tuple Int | TupleType | ListType | Infix Int | Infixr Int | Prefix | Postfix | Gyrator deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Tm f v) where
  pPrintPrec l p (Var x) = pPrintPrec l p x
  pPrintPrec l p (Fun f xs) =
    pPrintStyle (termStyle f) l p (pPrint f) xs

instance (PrettyTerm f, Pretty v) => Pretty (Rule f v) where
  pPrint (Rule l r) =
    hang (pPrint l <+> text "->") 2 (pPrint r)

pPrintStyle :: Pretty a => TermStyle -> PrettyLevel -> Rational -> Doc -> [a] -> Doc
pPrintStyle Invisible l p d [] = d
pPrintStyle Invisible l p _ [t] = pPrintPrec l p t
pPrintStyle Invisible l p _ (t:ts) =
  pPrintParen (p > 10) $
    hang (pPrint t) 2
      (fsep (map (pPrintPrec l 11) ts))
pPrintStyle Curried l p d [] = d
pPrintStyle Curried l p d xs =
  pPrintParen (p > 10) $
    hang d 2
      (fsep (map (pPrintPrec l 11) xs))
pPrintStyle Uncurried l p d [] = d
pPrintStyle Uncurried l p d xs =
  d <> parens (fsep (punctuate comma (map (pPrintPrec l 0) xs)))
pPrintStyle (Tuple arity) l p d xs
  | length xs >= arity =
    pPrintStyle Curried l p
      (pPrintTuple (take arity (map (pPrintPrec l 0) xs)))
      (drop arity xs)
  | otherwise =
    pPrintStyle Curried l p
      (text ("(" ++ replicate (arity-1) ',' ++ ")")) xs
pPrintStyle Postfix l p d [x] =
  pPrintPrec l 11 x <> d
pPrintStyle Postfix l p d xs =
  pPrintStyle Curried l p (parens d) xs
pPrintStyle Prefix l p d [x] =
  d <> pPrintPrec l 11 x
pPrintStyle Prefix l p d xs =
  pPrintStyle Curried l p (parens d) xs
pPrintStyle TupleType l p d xs =
  pPrintStyle (Tuple (length xs)) l p d xs
pPrintStyle ListType l p d [x] =
  brackets (pPrintPrec l 0 x)
pPrintStyle ListType l p d xs =
  pPrintStyle Curried l p d xs
pPrintStyle Gyrator l p d [x, y] =
  d <> brackets (sep (punctuate comma [pPrintPrec l 0 x, pPrintPrec l 0 y]))
pPrintStyle Gyrator l p d (x:y:zs) =
  pPrintStyle Curried l p (pPrintStyle Gyrator l p d [x, y]) zs
pPrintStyle Gyrator l p d xs = pPrintStyle Curried l p d xs
pPrintStyle style l p d xs =
  case xs of
    [x, y] ->
      pPrintParen (p > pOp) $
        hang (pPrintPrec l (pOp+1) x <+> d) 2
             (pPrintPrec l (pOp+r) y)
    (x:y:xs) ->
      pPrintParen (p > pOp) $
        hang (pPrintStyle style l 11 d [x, y]) 2
          (fsep (map (pPrintPrec l 11) xs))
    [x] ->
      parens (pPrintPrec l (pOp+1) x <+> d)
    _ ->
      pPrintParen (p > pOp) $
        hang (parens d) 2
          (fsep (map (pPrintPrec l 11) xs))
  where
    (r, pOp) =
      case style of
        Infixr pOp -> (0, fromIntegral pOp)
        Infix  pOp -> (1, fromIntegral pOp)
