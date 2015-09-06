{-# OPTIONS_GHC -funfolding-creation-threshold=1000000 -funfolding-use-threshold=100000 #-}
module KBC.Term.Nested where

import qualified KBC.Term as Flat
import Data.Either

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

-- Turn a compound term into a flatterm.
flatten :: Term f -> Flat.Term f
flatten (Flat t) = t
flatten t =
  Flat.buildTerm $ do
    let
      -- Nothing: no substitution
      -- Just (Left sub): a substitution
      -- Just (Right sub): a triangle substitution
      loop Nothing (Flat t) = Flat.emitTerm t
      loop (Just sub) (Flat t) = emitSubst sub (Flat.singleton t)
      loop sub (Subst sub' t) = loop (combine sub (Left sub')) t
      loop sub (IterSubst sub' t) = loop (combine sub (Right sub')) t
      loop Nothing (Var x) = Flat.emitVar x
      loop (Just sub) (Var x)
        | Just t <- Flat.lookupList (either id Flat.unTriangle sub) x =
          emitSubst sub t
      loop sub (Fun f ts) = Flat.emitFun f (mapM_ (loop sub) ts)

      emitSubst (Left sub) t = Flat.emitSubstList sub t
      emitSubst (Right sub) t = Flat.emitIterSubstList sub t

      combine Nothing sub = Just sub
      combine (Just sub) sub' =
        Just (Left (toSub sub' `Flat.substCompose` toSub sub))

      toSub (Left sub) = sub
      toSub (Right sub) = Flat.close sub

    loop Nothing t
