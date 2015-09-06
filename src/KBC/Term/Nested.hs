{-# OPTIONS_GHC -funfolding-creation-threshold=1000000 -funfolding-use-threshold=100000 #-}
module KBC.Term.Nested where

import qualified KBC.Term as Flat
import Data.Either

--------------------------------------------------------------------------------
-- A helper datatype for building terms.
--------------------------------------------------------------------------------

-- An algebraic data type for terms, with flatterms at the leaf.
data Term f =
    Flat {-# UNPACK #-} !(Flat.TermList f)
  | Subst {-# UNPACK #-} !(Flat.Subst f) (Term f)
  | IterSubst {-# UNPACK #-} !(Flat.Subst f) (Term f)
  | Var {-# UNPACK #-} !Flat.Var
  | Fun {-# UNPACK #-} !(Flat.Fun f) (Term f)
  | Nil
  | Append (Term f) (Term f)

fromList :: [Term f] -> Term f
fromList = foldr Append Nil

-- Turn a compound term into a flatterm.
flatten :: Term f -> Flat.Term f
flatten t =
  case flattenList t of
    Flat.Cons u Flat.Empty -> u

-- Turn a compound termlist into a flatterm list.
flattenList :: Term f -> Flat.TermList f
flattenList (Flat t) = t
flattenList t =
  Flat.buildTermList $ do
    let
      -- Nothing: no substitution
      -- Just (Left sub): a substitution
      -- Just (Right sub): a triangle substitution
      loop Nothing (Flat t) = Flat.emitTermList t
      loop (Just sub) (Flat t) = emitSubst sub t
      loop sub (Subst sub' t) = loop (combine sub (Left sub')) t
      loop sub (IterSubst sub' t) = loop (combine sub (Right sub')) t
      loop Nothing (Var x) = Flat.emitVar x
      loop (Just sub) (Var x)
        | Just t <- Flat.lookupList (either id id sub) x =
          emitSubst sub t
      loop sub (Fun f t) = Flat.emitFun f (loop sub t)
      loop _ Nil = return ()
      loop sub (Append t u) = do
        loop sub t
        loop sub u

      emitSubst (Left sub) t = Flat.emitSubstList sub t
      emitSubst (Right sub) t = Flat.emitIterSubstList sub t

      combine Nothing sub = Just sub
      combine (Just sub) sub' =
        Just (Left (toSub sub' `Flat.substCompose` toSub sub))

      toSub (Left sub) = sub
      toSub (Right sub) = Flat.close sub

    loop Nothing t
