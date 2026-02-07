{-# LANGUAGE TypeFamilies, BangPatterns, PatternSynonyms, ViewPatterns #-}
module Twee.Term.Nested where

import qualified Twee.Term as Flat
import qualified Twee.Term.Core as Flat
import Twee.Term(Var, Fun, Build(..))

data TermList f =
    Nil
  | AppendTerm (Term f) (TermList f)
  | AppendFlatList {-# UNPACK #-} !(Flat.TermList f) (TermList f) -- first argument must be non-empty

flatList :: Flat.TermList f -> TermList f
flatList Flat.Nil = Nil
flatList t = AppendFlatList t Nil

(+++) :: TermList f -> TermList f -> TermList f
Nil +++ ts = ts
AppendTerm t ts +++ us = AppendTerm t (ts +++ us)
AppendFlatList t ts +++ us = AppendFlatList t (ts +++ us)

data Term f =
    Flat {-# UNPACK #-} !(Flat.Term f)
  | VarTerm {-# UNPACK #-} !Var
  | AppTerm {-# UNPACK #-} !(Fun f) (TermList f)

singleton :: Term f -> TermList f
singleton t = AppendTerm t Nil

instance Build (TermList f) where
  type BuildFun (TermList f) = f
  builder Nil = mempty
  builder (AppendTerm t us) = builder t `mappend` builder us
  builder (AppendFlatList ts us) = builder ts `mappend` builder us

instance Build (Term f) where
  type BuildFun (Term f) = f
  builder (Flat t) = builder t
  builder (VarTerm x) = Flat.var x
  builder (AppTerm f ts) = Flat.app f (builder ts)

lenList :: TermList f -> Int
lenList t = aux 0 [t]
  where
    aux !_ !_ | False = undefined
    aux n [] = n
    aux n (Nil:ts) = aux n ts
    aux n (AppendFlatList t u:ts) = aux (n+Flat.lenList t) (u:ts)
    aux n (AppendTerm (Flat t) u:ts) = aux (n+Flat.len t) (u:ts)
    aux n (AppendTerm VarTerm{} u:ts) = aux (n+1) (u:ts)
    aux n (AppendTerm (AppTerm f t) u:ts) = aux (n+1) (t:u:ts)

len :: Term f -> Int
len t = lenList (singleton t)

flattenList :: TermList f -> Flat.TermList f
flattenList t = Flat.buildTermList (lenList t) (builder t)

flatten :: Term f -> Flat.Term f
flatten t =
  case Flat.buildTermList (len t) (builder (singleton t)) of
    Flat.Cons u Flat.Nil -> u

toTerm :: TermList f -> Term f
toTerm (AppendFlatList t Nil)
  | Flat.Cons u Flat.Nil <- t = Flat u
toTerm (AppendTerm t Nil) = t
toTerm _ = error "toTerm: not a singleton term"

patHead :: TermList f -> Maybe (Term f, TermList f, TermList f)
patHead Nil = Nothing
patHead (AppendFlatList t ts) =
  let (t, us, vs) = Flat.unsafePatHead (Flat.singleton t) in
  Just (Flat t, AppendFlatList us ts, AppendFlatList vs ts) 
patHead (AppendTerm t@VarTerm{} ts) =
  Just (t, ts, ts)
patHead (AppendTerm t@(AppTerm f ts) us) =
  Just (t, us, ts +++ us)

pattern ConsSym :: Term f -> TermList f -> TermList f -> TermList f
pattern ConsSym{hd, tl, rest} <- (patHead -> Just (hd, tl, rest))

pattern Var :: Var -> Term f
pattern Var x <- (patVar -> Just x)
  where
    Var x = VarTerm x

patVar :: Term f -> Maybe Var
patVar (VarTerm x) = Just x
patVar (Flat (Flat.Var x)) = Just x
patVar _ = Nothing

patApp :: Term f -> Maybe (Fun f, TermList f)
patApp (AppTerm f ts) = Just (f, ts)
patApp (Flat (Flat.App f ts)) = Just (f, flatList ts)
patApp _ = Nothing

pattern App :: Fun f -> TermList f -> Term f
pattern App f ts <- (patApp -> Just (f, ts))
  where
    App f ts = AppTerm f ts
