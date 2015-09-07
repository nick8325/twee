{-# LANGUAGE CPP #-}
module KBC.Term.Nested where

#include "errors.h"
import qualified KBC.Term as Flat
import Data.Either
import Data.Maybe

--------------------------------------------------------------------------------
-- A helper datatype for building terms.
--------------------------------------------------------------------------------

-- An algebraic data type for terms, with flatterms at the leaf.
data Term f =
    Flat {-# UNPACK #-} !(Flat.Term f)
  | Subst {-# UNPACK #-} !(Flat.Subst f) (Term f)
  | IterSubst {-# UNPACK #-} !(Flat.TriangleSubst f) (Term f)
  | Var {-# UNPACK #-} !Flat.Var
  | Fun {-# UNPACK #-} !(Flat.Fun f) [Term f]

instance Show f => Show (Term f) where show = show . flatten

-- Turn a compound term into a flatterm.
flatten :: Term f -> Flat.Term f
flatten t =
  case flattenList [t] of
    Flat.Cons u Flat.Empty -> u

-- Turn a compound term list into a flatterm list.
flattenList :: [Term f] -> Flat.TermList f
flattenList [Flat t] = Flat.singleton t
flattenList ts =
  {-# SCC flattenList #-}
  Flat.buildTermList 32 $ do
    let
      -- Nothing: no substitution
      -- Just (Left sub): a substitution
      -- Just (Right sub): a triangle substitution
      loop Nothing (Flat t) = Flat.emitTerm t
      loop (Just (Left sub)) (Flat t) = Flat.emitSubst sub t
      loop (Just (Right sub)) (Flat t) = Flat.emitIterSubst sub t
      loop sub (Subst sub' t) = loop (combine sub (Left sub')) t
      loop sub (IterSubst sub' t) = loop (combine sub (Right sub')) t
      loop Nothing (Var x) = Flat.emitVar x
      loop (Just (Left sub)) (Var x) =
        case Flat.lookupList sub x of
          Nothing -> Flat.emitVar x
          Just t  -> Flat.emitTermList t
      loop (Just (Right sub)) (Var x) =
        case Flat.lookupList (Flat.unTriangle sub) x of
          Nothing -> Flat.emitVar x
          Just t  -> Flat.emitIterSubstList sub t
      loop sub (Fun f ts) = Flat.emitFun f (mapM_ (loop sub) ts)

      combine Nothing sub = Just sub
      combine (Just sub) sub' =
        Just (Left (toSub sub' `Flat.substCompose` toSub sub))

      toSub (Left sub) = sub
      toSub (Right sub) = Flat.close sub

    mapM_ (loop Nothing) ts

-- Turn a substitution list into a substitution.
flattenSubst :: [(Flat.Var, Term f)] -> Flat.Subst f
flattenSubst sub = fromMaybe err (Flat.matchList pat t)
  where
    pat = flattenList (map (Var . fst) sub)
    t   = flattenList (map snd sub)
    err = ERROR("variable bound to two different terms")
