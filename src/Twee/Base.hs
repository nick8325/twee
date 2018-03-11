-- | Useful operations on terms and similar. Also re-exports some generally
-- useful modules such as 'Twee.Term' and 'Twee.Pretty'.

{-# LANGUAGE TypeFamilies, FlexibleInstances, UndecidableInstances, DeriveFunctor, DefaultSignatures, FlexibleContexts, TypeOperators, MultiParamTypeClasses, GeneralizedNewtypeDeriving, ConstraintKinds, RecordWildCards #-}
module Twee.Base(
  -- * Re-exported functionality
  module Twee.Term, module Twee.Pretty,
  -- * The 'Symbolic' typeclass
  Symbolic(..), subst, terms,
  TermOf, TermListOf, SubstOf, TriangleSubstOf, BuilderOf, FunOf,
  vars, isGround, funs, occ, occVar, canonicalise, renameAvoiding,
  -- * General-purpose functionality
  Id(..), Has(..),
  -- * Typeclasses
  Minimal(..), minimalTerm, isMinimal, erase,
  Skolem(..), Arity(..), Sized(..), Ordered(..), lessThan, orientTerms, EqualsBonus(..), Strictness(..), Function, Extended(..)) where

import Prelude hiding (lookup)
import Control.Monad
import qualified Data.DList as DList
import Twee.Term hiding (subst, canonicalise)
import qualified Twee.Term as Term
import Twee.Pretty
import Twee.Constraints hiding (funs)
import Data.DList(DList)
import Data.Typeable
import Data.Int
import Data.Maybe
import qualified Data.IntMap.Strict as IntMap

-- | Represents a unique identifier (e.g., for a rule).
newtype Id = Id { unId :: Int32 }
  deriving (Eq, Ord, Show, Enum, Bounded, Num, Real, Integral)

instance Pretty Id where
  pPrint = text . show . unId

-- | Generalisation of term functionality to things that contain terms (e.g.,
-- rewrite rules and equations).
class Symbolic a where
  type ConstantOf a

  -- | Compute a 'DList' of all terms which appear in the argument
  -- (used for e.g. computing free variables).
  -- See also 'terms'.
  termsDL :: a -> DList (TermListOf a)

  -- | Apply a substitution.
  -- When using the 'Symbolic' type class, you can use 'subst' instead.
  subst_ :: (Var -> BuilderOf a) -> a -> a

-- | Apply a substitution.
subst :: (Symbolic a, Substitution s, SubstFun s ~ ConstantOf a) => s -> a -> a
subst sub x = subst_ (evalSubst sub) x

-- | Find all terms occuring in the argument.
terms :: Symbolic a => a -> [TermListOf a]
terms = DList.toList . termsDL

-- | A term compatible with a given 'Symbolic'.
type TermOf a = Term (ConstantOf a)
-- | A termlist compatible with a given 'Symbolic'.
type TermListOf a = TermList (ConstantOf a)
-- | A substitution compatible with a given 'Symbolic'.
type SubstOf a = Subst (ConstantOf a)
-- | A triangle substitution compatible with a given 'Symbolic'.
type TriangleSubstOf a = TriangleSubst (ConstantOf a)
-- | A builder compatible with a given 'Symbolic'.
type BuilderOf a = Builder (ConstantOf a)
-- | The underlying type of function symbols of a given 'Symbolic'.
type FunOf a = Fun (ConstantOf a)

instance Symbolic (Term f) where
  type ConstantOf (Term f) = f
  termsDL = return . singleton
  subst_ sub = build . Term.subst sub

instance Symbolic (TermList f) where
  type ConstantOf (TermList f) = f
  termsDL = return
  subst_ sub = buildList . Term.substList sub

instance Symbolic (Subst f) where
  type ConstantOf (Subst f) = f
  termsDL (Subst sub) = termsDL (IntMap.elems sub)
  subst_ sub (Subst s) = Subst (fmap (subst_ sub) s)

instance (ConstantOf a ~ ConstantOf b, Symbolic a, Symbolic b) => Symbolic (a, b) where
  type ConstantOf (a, b) = ConstantOf a
  termsDL (x, y) = termsDL x `mplus` termsDL y
  subst_ sub (x, y) = (subst_ sub x, subst_ sub y)

instance (ConstantOf a ~ ConstantOf b,
          ConstantOf a ~ ConstantOf c,
          Symbolic a, Symbolic b, Symbolic c) => Symbolic (a, b, c) where
  type ConstantOf (a, b, c) = ConstantOf a
  termsDL (x, y, z) = termsDL x `mplus` termsDL y `mplus` termsDL z
  subst_ sub (x, y, z) = (subst_ sub x, subst_ sub y, subst_ sub z)

instance Symbolic a => Symbolic [a] where
  type ConstantOf [a] = ConstantOf a
  termsDL xs = msum (map termsDL xs)
  subst_ sub xs = map (subst_ sub) xs

instance Symbolic a => Symbolic (Maybe a) where
  type ConstantOf (Maybe a) = ConstantOf a
  termsDL Nothing = mzero
  termsDL (Just x) = termsDL x
  subst_ sub x = fmap (subst_ sub) x

-- | An instance @'Has' a b@ indicates that a value of type @a@ contains a value
-- of type @b@ which is somehow part of the meaning of the @a@.
--
-- A number of functions use 'Has' constraints to work in a more general setting.
-- For example, the functions in 'Twee.CP' operate on rewrite rules, but actually
-- accept any @a@ satisfying @'Has' a ('Twee.Rule.Rule' f)@.
--
-- Use taste when definining 'Has' instances; don't do it willy-nilly.
class Has a b where
  -- | Get at the thing.
  the :: a -> b

instance Has a a where
  the = id

-- | Find the variables occurring in the argument.
{-# INLINE vars #-}
vars :: Symbolic a => a -> [Var]
vars x = [ v | t <- DList.toList (termsDL x), Var v <- subtermsList t ]

-- | Test if the argument is ground.
{-# INLINE isGround #-}
isGround :: Symbolic a => a -> Bool
isGround = null . vars

-- | Find the function symbols occurring in the argument.
{-# INLINE funs #-}
funs :: Symbolic a => a -> [FunOf a]
funs x = [ f | t <- DList.toList (termsDL x), App f _ <- subtermsList t ]

-- | Count how many times a function symbol occurs in the argument.
{-# INLINE occ #-}
occ :: Symbolic a => FunOf a -> a -> Int
occ x t = length (filter (== x) (funs t))

-- | Count how many times a variable occurs in the argument.
{-# INLINE occVar #-}
occVar :: Symbolic a => Var -> a -> Int
occVar x t = length (filter (== x) (vars t))

-- | Rename the argument so that variables are introduced in a canonical order
-- (starting with V0, then V1 and so on).
{-# INLINEABLE canonicalise #-}
canonicalise :: Symbolic a => a -> a
canonicalise t = subst sub t
  where
    sub = Term.canonicalise (DList.toList (termsDL t))

-- | Rename the second argument so that it does not mention any variable which
-- occurs in the first.
{-# INLINEABLE renameAvoiding #-}
renameAvoiding :: (Symbolic a, Symbolic b) => a -> b -> b
renameAvoiding x y
  | x2 < y1 || y2 < x1 =
    -- No overlap. Important in the case when x is ground,
    -- in which case x2 == minBound and the calculation below doesn't work.
    y
  | otherwise =
    -- Map y1 to x2+1
    subst (\(V x) -> var (V (x-y1+x2+1))) y
  where
    (V x1, V x2) = boundLists (terms x)
    (V y1, V y2) = boundLists (terms y)

-- | Check if a term is the minimal constant.
isMinimal :: Minimal f => Term f -> Bool
isMinimal (App f Empty) | f == minimal = True
isMinimal _ = False

-- | Build the minimal constant as a term.
minimalTerm :: Minimal f => Term f
minimalTerm = build (con minimal)

-- | Erase a given set of variables from the argument, replacing them with the
-- minimal constant.
erase :: (Symbolic a, ConstantOf a ~ f, Minimal f) => [Var] -> a -> a
erase [] t = t
erase xs t = subst sub t
  where
    sub = fromMaybe undefined $ listToSubst [(x, minimalTerm) | x <- xs]

-- | Construction of Skolem constants.
class Skolem f where
  -- | Turn a variable into a Skolem constant.
  skolem  :: Var -> Fun f
  getSkolem :: Fun f -> Maybe Var

-- | For types which have a notion of arity.
class Arity f where
  -- | Measure the arity.
  arity :: f -> Int

instance Arity f => Arity (Fun f) where
  arity = arity . fun_value

-- | For types which have a notion of size.
class Sized a where
  -- | Compute the size.
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

-- | The collection of constraints which the type of function symbols must
-- satisfy in order to be used by twee.
type Function f = (Ordered f, Arity f, Sized f, Minimal f, Skolem f, PrettyTerm f, EqualsBonus f)

-- | A hack for encoding Horn clauses. See 'Twee.CP.Score'.
-- The default implementation of 'hasEqualsBonus' should work OK.
class EqualsBonus f where
  hasEqualsBonus :: f -> Bool
  hasEqualsBonus _ = False
  isEquals, isTrue, isFalse :: f -> Bool
  isEquals _ = False
  isTrue _ = False
  isFalse _ = False

instance EqualsBonus f => EqualsBonus (Fun f) where
  hasEqualsBonus = hasEqualsBonus . fun_value
  isEquals = isEquals . fun_value
  isTrue = isTrue . fun_value
  isFalse = isFalse . fun_value

-- | A function symbol extended with a minimal constant and Skolem functions.
-- Comes equipped with 'Minimal' and 'Skolem' instances.
data Extended f =
    -- | The minimal constant.
    Minimal
    -- | A Skolem function.
  | Skolem Var
    -- | An ordinary function symbol.
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
  getSkolem (F (Skolem x)) = Just x
  getSkolem _ = Nothing

instance EqualsBonus f => EqualsBonus (Extended f) where
  hasEqualsBonus (Function f) = hasEqualsBonus f
  hasEqualsBonus _ = False
  isEquals (Function f) = isEquals f
  isEquals _ = False
  isTrue (Function f) = isTrue f
  isTrue _ = False
  isFalse (Function f) = isFalse f
  isFalse _ = False
