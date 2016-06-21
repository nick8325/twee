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
    here   :: [Entry a],
    fun    :: {-# UNPACK #-} !(Array (Index a)),
    var    :: !(Index a) } |
  Nil
  deriving Show

instance Default (Index a) where def = Nil

data Entry a =
  Entry {
    e_key   :: {-# UNPACK #-} !(TermOf a),
    e_value :: a }
  deriving (Eq, Show)

{-# INLINE null #-}
null :: Index a -> Bool
null Nil = True
null _ = False

{-# INLINEABLE singleton #-}
singleton :: Symbolic a => a -> Index a
singleton x = singletonEntry (Term.singleton t) (Entry t x)
  where
    t = term x

{-# INLINE singletonEntry #-}
singletonEntry :: TermListOf a -> Entry a -> Index a
singletonEntry t e =
  Index 0 t [e] newArray Nil

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
    aux t@(ConsSym (Var _) u) idx =
      idx {
        size = lenList t `min` size idx,
        var  = aux u (var idx) }
    t  = term x0
    x  = Entry t x0

{-# INLINE expand #-}
expand :: Index a -> Index a
expand idx@Index{prefix = ConsSym t ts} =
  case t of
    Var _ ->
      Index (size idx + 1 + lenList ts) emptyTermList [] newArray
        idx { prefix = ts }
    Fun (MkFun f _) us ->
      Index (size idx + 1 + lenList ts) emptyTermList []
        (update f idx { prefix = ts } newArray)
        Nil

toKey :: TermList a -> TermList a
toKey = buildList . aux
  where
    aux Empty = mempty
    aux (ConsSym (Fun f _) t) =
      con f `mappend` aux t
    aux (ConsSym (Var _) t) =
      Term.var (MkVar 0) `mappend` aux t

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
    aux (ConsSym (Var _) t) idx =
      idx { var = aux t (var idx) }
    t  = term x0
    x  = Entry t x0

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
    aux (ConsSym (Var _) t) idx = aux t (var idx)
    t  = term x0
    x  = Entry t x0

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
freeze idx = Frozen $ \t -> find t idx []

find :: TermListOf a -> Index a -> [Match a] -> [Match a]
find t idx xs = stamp "finding first match in index" (aux t idx xs)
  where
    {-# INLINE aux #-}
    aux !_ !_ _ | False = __
    aux _ Nil rest = rest
    aux t Index{size = size, prefix = prefix} rest
      | lenList t < size + lenList prefix = rest
    aux t Index{..} rest =
      pref t prefix here fun var rest

    pref !_ !_ _ !_ _ _ | False = __
    pref Empty Empty here _ _ rest = try here rest
    pref Empty _ _ _ _ _ = __
    pref (Cons _ ts) (Cons (Var _) us) here fun var rest =
      pref ts us here fun var rest
    pref (ConsSym (Fun f _) ts) (ConsSym (Fun g _) us) here fun var rest
      | f == g = pref ts us here fun var rest
    pref _ (Cons _ _) _ _ _ rest = rest
    pref t@(ConsSym (Fun (MkFun n _) _) ts) Empty _ fun var rest =
      aux us var (aux ts (fun ! n) rest)
      where
        Cons _ us = t
    pref (Cons _ ts) Empty _ _ var rest = aux ts var rest

    {-# INLINE try #-}
    try [] rest = rest
    try xs rest =
      stamp "find in index" $
      [ Match x sub
      | Entry u x <- xs,
        sub <- maybeToList (matchList (Term.singleton u) t) ] ++
      rest

elems :: Index a -> [a]
elems Nil = []
elems idx =
  Prelude.map e_value (here idx) ++
  concatMap elems (Prelude.map snd (toList (fun idx))) ++
  elems (var idx)

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
