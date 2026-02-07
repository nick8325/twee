{-# LANGUAGE TypeFamilies, BangPatterns, PatternSynonyms, ViewPatterns #-}
module Twee.Term.Nested where

import qualified Twee.Term as Flat
import qualified Twee.Term.Core as Flat
import Twee.Term(Var, Fun, Build(..))

data Term f =
    Flat {-# UNPACK #-} !(Flat.Term f)
  | VarTerm {-# UNPACK #-} !Var
  | AppTerm {-# UNPACK #-} !(Fun f) ![Term f]

instance Build (Term f) where
  type BuildFun (Term f) = f
  builder (Flat t) = builder t
  builder (VarTerm x) = Flat.var x
  builder (AppTerm f ts) = Flat.app f (builder ts)

len :: Term f -> Int
len t = aux 0 [t] []
  where
    aux !_ !_ !_ | False = undefined
    aux n [] [] = n
    aux n [] (ts:tss) = aux n ts tss
    aux n (Flat t:ts) tss = aux (n+Flat.len t) ts tss
    aux n (VarTerm _:ts) tss = aux (n+1) ts tss
    aux n (AppTerm _ ts:us) tss = aux (n+1) ts (us:tss)

flatten :: Term f -> Flat.Term f
flatten t =
  case Flat.buildTermList (len t) (builder t) of
    Flat.Cons u Flat.Nil -> u

pattern Var :: Var -> Term f
pattern Var x <- (patVar -> Just x)
  where
    Var x = VarTerm x

pattern App :: Fun f -> [Term f] -> Term f
pattern App f ts <- (patApp -> Just (f, ts))
  where
    App f ts = AppTerm f ts

patVar :: Term f -> Maybe Var
patVar (VarTerm x) = Just x
patVar (Flat (Flat.Var x)) = Just x
patVar _ = Nothing

patApp :: Term f -> Maybe (Fun f, [Term f])
patApp (AppTerm f ts) = Just (f, ts)
patApp (Flat (Flat.App f ts)) = Just (f, map Flat (Flat.unpack ts))
patApp _ = Nothing
