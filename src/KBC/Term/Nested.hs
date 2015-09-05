{-# OPTIONS_GHC -funfolding-creation-threshold=1000000 -funfolding-use-threshold=100000 #-}
module KBC.Term.Nested where

import qualified KBC.Term as Flat

--------------------------------------------------------------------------------
-- A helper datatype for building terms.
--------------------------------------------------------------------------------

-- An algebraic data type for terms, with flatterms at the leaf.
data Term f =
    Flat {-# UNPACK #-} !(Flat.TermList f)
  | Subst {-# UNPACK #-} !(Flat.Subst f) {-# UNPACK #-} !(Flat.TermList f)
  | IterSubst {-# UNPACK #-} !(Flat.Subst f) {-# UNPACK #-} !(Flat.TermList f)
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
      loop (Flat t) = Flat.emitTermList t
      loop (Subst sub t) = Flat.emitSubstList sub t
      loop (IterSubst sub t) = Flat.emitIterSubstList sub t
      loop (Var x) = Flat.emitVar x
      loop (Fun f t) = Flat.emitFun f (loop t)
      loop Nil = return ()
      loop (Append t u) = do
        loop t
        loop u
    loop t
