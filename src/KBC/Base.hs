{-# LANGUAGE TypeSynonymInstances, TypeFamilies, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, CPP #-}
module KBC.Base(
  Symbolic(..), term, termLists, varsDL, vars, funsDL, funs,
  canonicalise,
  Minimal(..), minimalTerm,
  Skolem(..), skolemConst, skolemise,
  Arity(..), Sized(..), SizedFun(..), Ordered(..), Strictness(..), Function,
  module KBC.Term, module KBC.Pretty) where

#include "errors.h"
import Control.Monad
import qualified Data.DList as DList
import Data.DList(DList)
import Data.List
import qualified Data.Map as Map
import KBC.Term hiding (subst, canonicalise)
import qualified KBC.Term as Term
import KBC.Pretty
import Text.PrettyPrint.HughesPJClass hiding (empty)
import Data.Ord
import {-# SOURCE #-} KBC.Constraints

-- Generalisation of term functionality to things that contain terms.
class Symbolic a where
  {-# MINIMAL (termList|termListsDL), subst #-}
  type ConstantOf a

  termList :: a -> TermListOf a
  termList t = DList.head (termListsDL t)

  termListsDL :: a -> DList (TermListOf a)
  termListsDL t = return (termList t)

  subst :: Subst (ConstantOf a) -> a -> a

term :: Symbolic a => a -> TermOf a
term x = t
  where
    Cons t Empty = termList x

termLists :: Symbolic a => a -> [TermListOf a]
termLists = DList.toList . termListsDL

type TermOf a = Term (ConstantOf a)
type TermListOf a = TermList (ConstantOf a)
type SubstOf a = Subst (ConstantOf a)

instance Symbolic (Term f) where
  type ConstantOf (Term f) = f
  termList = singleton
  subst    = Term.subst

instance (ConstantOf a ~ ConstantOf b,
          Symbolic a, Symbolic b) => Symbolic (a, b) where
  type ConstantOf (a, b) = ConstantOf a
  termListsDL (x, y) = termListsDL x `mplus` termListsDL y
  subst sub (x, y) = (subst sub x, subst sub y)

instance Symbolic a => Symbolic [a] where
  type ConstantOf [a] = ConstantOf a
  termListsDL ts = msum (map termListsDL ts)
  subst sub = map (subst sub)

vars :: Symbolic a => a -> [Var]
vars = DList.toList . varsDL

varsDL :: Symbolic a => a -> DList Var
varsDL t = termListsDL t >>= aux
  where
    aux Empty = mzero
    aux (ConsSym Fun{} t) = aux t
    aux (Cons (Var x) t) = return x `mplus` aux t

funs :: Symbolic a => a -> [Fun (ConstantOf a)]
funs = DList.toList . funsDL

funsDL :: Symbolic a => a -> DList (Fun (ConstantOf a))
funsDL t = termListsDL t >>= aux
  where
    aux Empty = mzero
    aux (ConsSym (Fun f _) t) = return f `mplus` aux t
    aux (Cons Var{} t) = aux t

canonicalise :: Symbolic a => a -> a
canonicalise t = subst (Term.canonicalise (termLists t)) t

class Minimal a where
  minimal :: Fun a

isMinimal :: Minimal f => Term f -> Bool
isMinimal (Fun f Empty) | f == minimal = True
isMinimal _ = False

minimalTerm :: Minimal f => Term f
minimalTerm = ERROR("try and eliminate as many uses of this as possible first")

class Skolem f where
  skolem  :: Int -> Fun f

skolemConst :: Skolem f => Int -> Term f
skolemConst n = fun (skolem n) []

skolemise :: Skolem f => Term f -> Term f
skolemise t = subst sub t
  where
    -- XXX export a (Var -> Term) substitution function
    Just sub =
      flattenSubst . CUnion $
        [CSingle (MkVar x) (skolemConst x) | MkVar x <- vars t]

class (PrettyTerm f, Minimal f, Skolem f, Arity f, SizedFun f, Ordered f) => Function f

class Arity f where
  arity :: Fun f -> Int

class Sized (Fun f) => SizedFun f
class Sized a where
  size  :: a -> Int

instance SizedFun f => Sized (TermList f) where
  size = aux 0
    where
      aux n Empty = n
      aux n (ConsSym (Fun f _) t) = aux (n+size f) t
      aux n (Cons (Var _) t) = aux (n+1) t

instance SizedFun f => Sized (Term f) where
  size = size . singleton

class Ord f => Ordered f where
  orientTerms :: Term f -> Term f -> Maybe Ordering
  orientTerms t u
    | t == u = Just EQ
    | lessEq t u = Just LT
    | lessEq u t = Just GT
    | otherwise = Nothing

  lessEq :: Term f -> Term f -> Bool
  lessIn :: Model f -> Term f -> Term f -> Bool

data Strictness = Strict | Nonstrict deriving (Eq, Show)
