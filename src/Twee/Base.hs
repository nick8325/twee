{-# LANGUAGE TypeFamilies, FlexibleInstances, CPP, UndecidableInstances, DeriveFunctor, DefaultSignatures, FlexibleContexts, DeriveGeneric, TypeOperators, MultiParamTypeClasses, GeneralizedNewtypeDeriving, ConstraintKinds #-}
-- To suppress a warning about hiding Arity
{-# OPTIONS_GHC -Wno-dodgy-imports #-}
module Twee.Base(
  Id(..), Symbolic(..), subst, GSymbolic(..), Has(..), terms, TermOf, TermListOf, SubstOf, TriangleSubstOf, BuilderOf, FunOf,
  vars, isGround, funs, occ, occVar, canonicalise, renameAvoiding,
  Minimal(..), minimalTerm, isMinimal,
  Skolem(..), Arity(..), Sized(..), Ordered(..), Equals(..), Strictness(..), Function, Extended(..),
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
import GHC.Generics hiding (Arity)
import Data.Typeable
import Data.Int

-- Represents a unique identifier (e.g., for a rule).
newtype Id = Id { unId :: Int32 }
  deriving (Eq, Ord, Show, Enum, Bounded, Num, Real, Integral)

-- Generalisation of term functionality to things that contain terms.
class Symbolic a where
  type ConstantOf a

  termsDL :: a -> DList (TermListOf a)
  default termsDL :: (Generic a, GSymbolic (ConstantOf a) (Rep a)) => a -> DList (TermListOf a)
  termsDL = gtermsDL . from
  subst_ :: (Var -> BuilderOf a) -> a -> a
  default subst_ :: (Generic a, GSymbolic (ConstantOf a) (Rep a)) => (Var -> BuilderOf a) -> a -> a
  subst_ sub = to . gsubst sub . from

class GSymbolic k f where
  gtermsDL :: f a -> DList (TermList k)
  gsubst :: (Var -> Builder k) -> f a -> f a

instance GSymbolic k V1 where
  gtermsDL _ = __
  gsubst _ x = x
instance GSymbolic k U1 where
  gtermsDL _ = mzero
  gsubst _ x = x
instance (GSymbolic k f, GSymbolic k g) => GSymbolic k (f :*: g) where
  gtermsDL (x :*: y) = gtermsDL x `mplus` gtermsDL y
  gsubst sub (x :*: y) = gsubst sub x :*: gsubst sub y
instance (GSymbolic k f, GSymbolic k g) => GSymbolic k (f :+: g) where
  gtermsDL (L1 x) = gtermsDL x
  gtermsDL (R1 x) = gtermsDL x
  gsubst sub (L1 x) = L1 (gsubst sub x)
  gsubst sub (R1 x) = R1 (gsubst sub x)
instance GSymbolic k f => GSymbolic k (M1 i c f) where
  gtermsDL (M1 x) = gtermsDL x
  gsubst sub (M1 x) = M1 (gsubst sub x)
instance (Symbolic a, ConstantOf a ~ k) => GSymbolic k (K1 i a) where
  gtermsDL (K1 x) = termsDL x
  gsubst sub (K1 x) = K1 (subst_ sub x)

subst :: (Symbolic a, Substitution s, SubstFun s ~ ConstantOf a) => s -> a -> a
subst sub x = subst_ (evalSubst sub) x

terms :: Symbolic a => a -> [TermListOf a]
terms = DList.toList . termsDL

type TermOf a = Term (ConstantOf a)
type TermListOf a = TermList (ConstantOf a)
type SubstOf a = Subst (ConstantOf a)
type TriangleSubstOf a = TriangleSubst (ConstantOf a)
type BuilderOf a = Builder (ConstantOf a)
type FunOf a = Fun (ConstantOf a)

instance Symbolic (Term f) where
  type ConstantOf (Term f) = f
  termsDL = return . singleton
  subst_ sub = build . Term.subst sub

instance Symbolic (TermList f) where
  type ConstantOf (TermList f) = f
  termsDL   = return
  subst_ sub = buildList . Term.substList sub

instance (ConstantOf a ~ ConstantOf b, Symbolic a, Symbolic b) => Symbolic (a, b) where
  type ConstantOf (a, b) = ConstantOf a

instance (ConstantOf a ~ ConstantOf b,
          ConstantOf a ~ ConstantOf c,
          Symbolic a, Symbolic b, Symbolic c) => Symbolic (a, b, c) where
  type ConstantOf (a, b, c) = ConstantOf a

instance Symbolic a => Symbolic [a] where
  type ConstantOf [a] = ConstantOf a

class Has a b where
  the :: a -> b

instance Has a a where
  the = id

{-# INLINE vars #-}
vars :: Symbolic a => a -> [Var]
vars x = [ v | t <- DList.toList (termsDL x), Var v <- subtermsList t ]

{-# INLINE isGround #-}
isGround :: Symbolic a => a -> Bool
isGround = null . vars

{-# INLINE funs #-}
funs :: Symbolic a => a -> [FunOf a]
funs x = [ f | t <- DList.toList (termsDL x), App f _ <- subtermsList t ]

{-# INLINE occ #-}
occ :: Symbolic a => FunOf a -> a -> Int
occ x t = length (filter (== x) (funs t))

{-# INLINE occVar #-}
occVar :: Symbolic a => Var -> a -> Int
occVar x t = length (filter (== x) (vars t))

{-# INLINEABLE canonicalise #-}
canonicalise :: Symbolic a => a -> a
canonicalise t = subst sub t
  where
    sub = Term.canonicalise (DList.toList (termsDL t))

{-# INLINEABLE renameAvoiding #-}
renameAvoiding :: (Symbolic a, Symbolic b) => a -> b -> b
renameAvoiding x y =
  subst (\(V x) -> var (V (x+n))) y
  where
    V n = maximum (V 0:map boundList (terms x))

isMinimal :: Minimal f => Term f -> Bool
isMinimal (App f Empty) | f == minimal = True
isMinimal _ = False

minimalTerm :: Minimal f => Term f
minimalTerm = build (con minimal)

class Skolem f where
  skolem  :: Var -> Fun f

class Arity f where
  arity :: f -> Int

instance Arity f => Arity (Fun f) where
  arity = arity . fun_value

class Sized a where
  size  :: a -> Int

instance Sized f => Sized (Fun f) where
  size = size . fun_value

instance Sized f => Sized (TermList f) where
  size = aux 0
    where
      aux n Empty = n
      aux n (ConsSym (App f _) t) = aux (n+size f) t
      aux n (Cons (Var _) t) = aux (n+1) t

instance Sized f => Sized (Term f) where
  size = size . singleton

type Function f = (Ordered f, Arity f, Sized f, Minimal f, Skolem f, PrettyTerm f, Equals f)

class Equals f where
  equalsCon, trueCon, falseCon :: Fun f

data Extended f =
    Minimal
  | Skolem Var
  | Function f
  deriving (Eq, Ord, Show, Functor)

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

instance (Typeable f, Ord f) => Minimal (Extended f) where
  minimal = fun Minimal

instance (Typeable f, Ord f) => Skolem (Extended f) where
  skolem x = fun (Skolem x)
