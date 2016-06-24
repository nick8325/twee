{-# LANGUAGE TypeFamilies, FlexibleInstances, CPP, UndecidableInstances, DeriveFunctor #-}
module Twee.Base(
  Symbolic(..), terms, subst, TermOf, TermListOf, SubstOf, BuilderOf, FunOf,
  vars, isGround, funs, occ, occVar, canonicalise,
  Minimal(..), minimalTerm, isMinimal,
  Skolem(..), Arity(..), Sized(..), Ordered(..), Strictness(..), Function, Extended(..),
  module Twee.Term, module Twee.Pretty) where

#include "errors.h"
import Prelude hiding (lookup)
import Control.Monad
import qualified Data.DList as DList
import Twee.Term hiding (subst, canonicalise)
import qualified Twee.Term as Term
import Twee.Pretty
import Twee.Constraints hiding (funs)
import Data.DList(DList)

-- Generalisation of term functionality to things that contain terms.
class Symbolic a where
  type ConstantOf a

  term    :: a -> TermOf a
  termsDL :: a -> DList (TermListOf a)
  replace :: (TermListOf a -> BuilderOf a) -> a -> a

terms :: Symbolic a => a -> [TermListOf a]
terms = DList.toList . termsDL

{-# INLINE subst #-}
subst :: (Symbolic a, Substitution s, SubstFun s ~ ConstantOf a) => s -> a -> a
subst sub x = replace (substList sub) x

type TermOf a = Term (ConstantOf a)
type TermListOf a = TermList (ConstantOf a)
type SubstOf a = Subst (ConstantOf a)
type BuilderOf a = Builder (ConstantOf a)
type FunOf a = Fun (ConstantOf a)

instance Symbolic (Term f) where
  type ConstantOf (Term f) = f
  term      = id
  termsDL   = return . singleton
  replace f = build . f . singleton

instance Symbolic (TermList f) where
  type ConstantOf (TermList f) = f
  term      = __
  termsDL   = return
  replace f = buildList . f

instance (ConstantOf a ~ ConstantOf b,
          Symbolic a, Symbolic b) => Symbolic (a, b) where
  type ConstantOf (a, b) = ConstantOf a
  term (x, _) = term x
  termsDL (x, y) = termsDL x `mplus` termsDL y
  replace f (x, y) = (replace f x, replace f y)

instance (ConstantOf a ~ ConstantOf b,
          ConstantOf a ~ ConstantOf c,
          Symbolic a, Symbolic b, Symbolic c) => Symbolic (a, b, c) where
  type ConstantOf (a, b, c) = ConstantOf a
  term (x, _, _) = term x
  termsDL (x, y, z) = termsDL x `mplus` termsDL y `mplus` termsDL z
  replace f (x, y, z) = (replace f x, replace f y, replace f z)

instance Symbolic a => Symbolic [a] where
  type ConstantOf [a] = ConstantOf a
  term _ = __
  termsDL = msum . map termsDL
  replace f = map (replace f)

{-# INLINE vars #-}
vars :: Symbolic a => a -> [Var]
vars x = [ v | t <- DList.toList (termsDL x), Var v <- subtermsList t ]

{-# INLINE isGround #-}
isGround :: Symbolic a => a -> Bool
isGround = null . vars

{-# INLINE funs #-}
funs :: Symbolic a => a -> [FunOf a]
funs x = [ f | t <- DList.toList (termsDL x), Fun f _ <- subtermsList t ]

{-# INLINE occ #-}
occ :: Symbolic a => FunOf a -> a -> Int
occ x t = length (filter (== x) (funs t))

{-# INLINE occVar #-}
occVar :: Symbolic a => Var -> a -> Int
occVar x t = length (filter (== x) (vars t))

canonicalise :: Symbolic a => a -> a
canonicalise t = replace (Term.substList sub) t
  where
    sub = Term.canonicalise (DList.toList (termsDL t))

isMinimal :: (Numbered f, Minimal f) => Term f -> Bool
isMinimal (Fun f Empty) | f == minimal = True
isMinimal _ = False

minimalTerm :: (Numbered f, Minimal f) => Term f
minimalTerm = build (con minimal)

class Skolem f where
  skolem  :: Var -> f

instance (Numbered f, Skolem f) => Skolem (Fun f) where
  skolem = toFun . skolem

class Arity f where
  arity :: f -> Int

instance (Numbered f, Arity f) => Arity (Fun f) where
  arity = arity . fromFun

class Sized a where
  size  :: a -> Int

instance (Sized f, Numbered f) => Sized (Fun f) where
  size = size . fromFun

instance (Sized f, Numbered f) => Sized (TermList f) where
  size = aux 0
    where
      aux n Empty = n
      aux n (ConsSym (Fun f _) t) = aux (n+size f) t
      aux n (Cons (Var _) t) = aux (n+1) t

instance (Sized f, Numbered f) => Sized (Term f) where
  size = size . singleton

class    (Numbered f, Ordered f, Arity f, Sized f, Minimal f, Skolem f, PrettyTerm f) => Function f
instance (Numbered f, Ordered f, Arity f, Sized f, Minimal f, Skolem f, PrettyTerm f) => Function f

data Extended f =
    Minimal
  | Skolem Var
  | Function f
  deriving (Eq, Ord, Show, Functor)

instance Minimal (Extended f) where
  minimal = Minimal

instance Skolem (Extended f) where
  skolem = Skolem

instance Numbered f => Numbered (Extended f) where
  toInt Minimal = 0
  toInt (Skolem (V n)) = 2*n+1
  toInt (Function f) = 2*toInt f+2

instance Pretty f => Pretty (Extended f) where
  pPrintPrec _ _ Minimal = text "?"
  pPrintPrec _ _ (Skolem (V n)) = text "sk" <> pPrint n
  pPrintPrec l p (Function f) = pPrintPrec l p f

instance PrettyTerm f => PrettyTerm (Extended f) where
  termStyle (Function f) = termStyle f
  termStyle _ = uncurried

instance Sized f => Sized (Extended f) where
  size (Function f) = size f
  size _ = 1

instance Arity f => Arity (Extended f) where
  arity (Function f) = arity f
  arity _ = 0
