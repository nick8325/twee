{-# LANGUAGE PatternSynonyms, ViewPatterns, BangPatterns #-}
module Twee.Term.Nested where

import qualified Twee.Term as Flat
import Twee.Term(Var(..), Fun(..), Subst)
import Control.Monad

data Term f =
    NVar {-# UNPACK #-} !(Var)
  | NApp {-# UNPACK #-} !(Fun f) [Term f]
  | Flat {-# UNPACK #-} !(Flat.Term f)
  deriving Show

{-# INLINE unpackTerm #-}
unpackTerm :: Term f -> Either Var (Fun f, [Term f])
unpackTerm (NVar x) = Left x
unpackTerm (NApp f ts) = Right (f, ts)
unpackTerm (Flat (Flat.Var x)) = Left x
unpackTerm (Flat (Flat.App f ts)) = Right (f, map Flat (Flat.unpack ts))

pattern Var x <- (unpackTerm -> Left x) where
  Var x = NVar x

pattern App f ts <- (unpackTerm -> Right (f, ts)) where
  App f ts = NApp f ts

flatten :: Term f -> Flat.Term f
flatten (Flat t) = t
flatten t = Flat.build (flat t)
  where
    flat (NVar x) = Flat.var x
    flat (NApp f ts) = Flat.app f (flatList ts)
    flat (Flat t) = Flat.builder t
    flatList [] = mempty
    flatList (t:ts) = flat t `mappend` flatList ts

match :: Term f -> Term f -> Maybe (Subst f)
match pat t = matchIn Flat.emptySubst pat t

matchIn :: Subst f -> Term f -> Term f -> Maybe (Subst f)
matchIn sub (Flat pat) (Flat t) = Flat.matchIn sub pat t
matchIn !sub (Var x) t = Flat.extend x (flatten t) sub
matchIn sub (App f ts) (App g us) = do
  guard (f == g)
  let
    loop sub [] [] = return sub
    loop sub (t:ts) (u:us) = do
      sub <- matchIn sub t u
      loop sub ts us
    loop _ _ _ = error "inconsistent arity"
  loop sub ts us
matchIn _ _ _ = Nothing
