-- Term indexing (perfect discrimination trees).
{-# LANGUAGE BangPatterns, CPP, TypeFamilies, RecordWildCards, OverloadedStrings #-}
-- We get some bogus warnings because of pattern synonyms.
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
{-# OPTIONS_GHC -funfolding-creation-threshold=1000000 -funfolding-use-threshold=1000000 #-}
module Twee.Index where

#include "errors.h"
import qualified Prelude
import Prelude hiding (filter, map, null)
import Twee.Base hiding (var, fun, empty, vars, size, singleton, prefix)
import qualified Twee.Term as Term
import Twee.Array
import qualified Data.List as List
import Data.Maybe
import Twee.Profile

data Index a =
  Index {
    size   :: {-# UNPACK #-} !Int, -- size of smallest term, not including prefix
    prefix :: {-# UNPACK #-} !(TermListOf a),
    here   :: [a],
    fun    :: {-# UNPACK #-} !(Array (Index a)),
    var    :: {-# UNPACK #-} !(Array (Index a)) } |
  Nil
  deriving Show

instance Default (Index a) where def = Nil

{-# INLINE null #-}
null :: Index a -> Bool
null Nil = True
null _ = False

{-# INLINEABLE singleton #-}
singleton :: Symbolic a => a -> Index a
singleton x = singletonEntry (Term.singleton (term x)) x

{-# INLINE singletonEntry #-}
singletonEntry :: TermListOf a -> a -> Index a
singletonEntry t x = Index 0 t [x] newArray newArray

{-# INLINE withPrefix #-}
withPrefix :: (ConstantOf a ~ f) => TermList f -> Index a -> Index a
withPrefix Empty idx = idx
withPrefix _ Nil = Nil
withPrefix t idx@Index{..} =
  idx{prefix = buildList (builder t `mappend` builder prefix)}

{-# INLINEABLE insert #-}
insert :: Symbolic a => a -> Index a -> Index a
insert x0 !idx = aux (toKey (Term.singleton t)) idx
  where
    aux t Nil = singletonEntry t x
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      withPrefix (Term.singleton t) (aux ts idx{prefix = us})
    aux t idx@Index{prefix = Cons{}} = aux t (expand idx)

    aux Empty idx =
      idx { size = 0, here = x:here idx }
    aux t@(ConsSym (Fun (MkFun f _) _) u) idx =
      idx {
        size = lenList t `min` size idx,
        fun  = update f idx' (fun idx) }
      where
        idx' = aux u (fun idx ! f)
    aux t@(ConsSym (Var (MkVar v)) u) idx =
      idx {
        size = lenList t `min` size idx,
        var  = update v idx' (var idx) }
      where
        idx' = aux u (var idx ! v)
    t = term x
    x = canonicalise x0

{-# INLINE expand #-}
expand :: Index a -> Index a
expand idx@Index{prefix = ConsSym t ts} =
  case t of
    Var (MkVar v) ->
      Index (size idx + 1 + lenList ts) emptyTermList [] newArray
        (update v idx { prefix = ts } newArray)
    Fun (MkFun f _) us ->
      Index (size idx + 1 + lenList ts) emptyTermList []
        (update f idx { prefix = ts } newArray) newArray

toKey :: TermList a -> TermList a
toKey = buildList . aux . canonicalise
  where
    aux Empty = mempty
    aux (ConsSym (Fun f _) t) =
      con f `mappend` aux t
    aux (ConsSym (Var x) t) =
      Term.var x `mappend` aux t

{-# INLINEABLE delete #-}
delete :: (Eq a, Symbolic a) => a -> Index a -> Index a
delete x0 !idx = aux (toKey (Term.singleton t)) idx
  where
    aux _ Nil = Nil
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      withPrefix (Term.singleton t) (aux ts idx{prefix = us})
    aux _ idx@Index{prefix = Cons{}} = idx

    aux Empty idx =
      idx { here = List.delete x (here idx) }
    aux (ConsSym (Fun (MkFun f _) _) t) idx =
      idx { fun = update f (aux t (fun idx ! f)) (fun idx) }
    aux (ConsSym (Var (MkVar v)) t) idx =
      idx { var = update v (aux t (var idx ! v)) (var idx) }
    t = term x
    x = canonicalise x0

{-# INLINEABLE elem #-}
elem :: (Eq a, Symbolic a) => a -> Index a -> Bool
elem x0 !idx = aux (toKey (Term.singleton t)) idx
  where
    aux _ Nil = False
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      aux ts idx{prefix = us}
    aux _ idx@Index{prefix = Cons{}} = False

    aux Empty idx = List.elem x (here idx)
    aux (ConsSym (Fun (MkFun f _) _) t) idx =
      aux t (fun idx ! f)
    aux (ConsSym (Var (MkVar v)) t) idx =
      aux t (var idx ! v)
    t = term x
    x = canonicalise x0

data Match a =
  Match {
    matchResult :: a,
    matchSubst  :: SubstOf a }

newtype Frozen a = Frozen { matchesList_ :: TermListOf a -> [Match a] }

matchesList :: TermListOf a -> Frozen a -> [Match a]
matchesList = flip matchesList_

{-# INLINEABLE lookup #-}
lookup :: Symbolic a => TermOf a -> Frozen a -> [a]
lookup t idx = stamp "lookup" [subst sub x | Match x sub <- matches t idx]

{-# INLINE matches #-}
matches :: TermOf a -> Frozen a -> [Match a]
matches t idx = stamp "finding first match in index" (matchesList (Term.singleton t) idx)

freeze :: Index a -> Frozen a
freeze idx = Frozen $ \t -> find t idx

find :: TermListOf a -> Index a -> [Match a]
find t idx = stamp "finding first match in index" (aux emptySubst t idx)
  where
    {-# INLINE aux #-}
    aux !_ !_ !_ | False = __
    aux _ _ Nil = []
    aux _ t Index{size = size, prefix = prefix}
      | lenList t < size + lenList prefix = []
    aux sub t Index{..} =
      pref sub t prefix here fun var

    pref !_ !_ !_ _ !_ !_ | False = __
    pref sub Empty Empty here _ _ = [ Match x sub | x <- here ]
    pref _ Empty _ _ _ _ = __
    pref sub (Cons t ts) (Cons (Var x) us) here fun var = do
      sub <- maybeToList (extend x t sub)
      pref sub ts us here fun var
    pref sub (ConsSym (Fun f _) ts) (ConsSym (Fun g _) us) here fun var
      | f == g = pref sub ts us here fun var
    pref _ _ (Cons _ _) _ _ _ = []
    pref sub t@(ConsSym (Fun (MkFun n _) _) ts) Empty _ fun var =
      tryVar sub t var ++ aux sub ts fn
      where
        !fn = fun ! n
    pref sub t@Cons{} Empty _ _ var = tryVar sub t var

    {-# INLINE tryVar #-}
    tryVar sub (UnsafeCons t ts) var = do
      (x, idx@Index{}) <- toList var
      sub <- maybeToList (extend (MkVar x) t sub)
      aux sub ts idx

elems :: Index a -> [a]
elems Nil = []
elems idx =
  here idx ++
  concatMap elems (Prelude.map snd (toList (fun idx))) ++
  concatMap elems (Prelude.map snd (toList (var idx)))

{-# INLINE map #-}
map :: (ConstantOf a ~ ConstantOf b) => (a -> b) -> Frozen a -> Frozen b
map f (Frozen matches) = Frozen $ \t -> [Match (f x) sub | Match x sub <- matches t]

{-# INLINE filter #-}
filter :: (a -> Bool) -> Frozen a -> Frozen a
filter p (Frozen matches) = Frozen $ \t ->
  [ m | m@(Match x _) <- matches t, p x ]

{-# INLINE union #-}
union :: Frozen a -> Frozen a -> Frozen a
union (Frozen f1) (Frozen f2) = Frozen $ \t -> f1 t ++ f2 t
