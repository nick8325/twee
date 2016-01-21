-- Term indexing (perfect discrimination trees).
{-# LANGUAGE BangPatterns, CPP, TypeFamilies, RecordWildCards #-}
-- We get some bogus warnings because of pattern synonyms.
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
{-# OPTIONS_GHC -funfolding-creation-threshold=1000000 -funfolding-use-threshold=1000000 #-}
module Twee.Index where

#include "errors.h"
import qualified Prelude
import Prelude hiding (filter, map, null)
import Twee.Base hiding (var, fun, empty, vars, size)
import qualified Twee.Term as Term
import Twee.Array
import qualified Data.List as List
import Data.Maybe

data Index a =
  Index {
    size :: {-# UNPACK #-} !Int,
    here :: [Entry a],
    fun  :: {-# UNPACK #-} !(Array (Index a)),
    var  :: !(Index a) } |
  Singleton {
    key   :: {-# UNPACK #-} !(TermListOf a),
    value :: {-# UNPACK #-} !(Entry a) } |
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
singleton x = Singleton (Term.singleton t) (Entry t x)
  where
    t = term x

{-# INLINEABLE insert #-}
insert :: Symbolic a => a -> Index a -> Index a
insert x0 !idx = aux (Term.singleton t) idx
  where
    aux t Nil = Singleton t x
    aux t (Singleton u x) = aux t (expand u x)
    aux Empty idx@Index{..} = idx { size = 0, here = x:here }
    aux t@(ConsSym (Fun (MkFun f) _) u) idx =
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
expand :: TermListOf a -> Entry a -> Index a
expand Empty x = Index 0 [x] newArray Nil
expand (ConsSym s t) x =
  Index (1+lenList t) [] fun var
  where
    (fun, var) =
      case s of
        Fun (MkFun f) _ ->
          (update f (Singleton t x) newArray, Nil)
        Var _ ->
          (newArray, Singleton t x)

{-# INLINEABLE delete #-}
delete :: (Eq a, Symbolic a) => a -> Index a -> Index a
delete x0 !idx = aux (Term.singleton t) idx
  where
    aux _ Nil = Nil
    aux t idx@(Singleton u y)
      | t == u && x == y = Nil
      | otherwise        = idx
    aux Empty idx = idx { here = List.delete x (here idx) }
    aux (ConsSym (Fun (MkFun f) _) t) idx =
      idx { fun = update f (aux t (fun idx ! f)) (fun idx) }
    aux (ConsSym (Var _) t) idx =
      idx { var = aux t (var idx) }
    t  = term x0
    x  = Entry t x0

{-# INLINEABLE elem #-}
elem :: (Eq a, Symbolic a) => a -> Index a -> Bool
elem x0 !idx = aux (Term.singleton t) idx
  where
    aux _ Nil = False
    aux t idx@(Singleton u y)
      | t == u && x == y = True
      | otherwise        = False
    aux Empty idx = List.elem x (here idx)
    aux (ConsSym (Fun (MkFun f) _) t) idx =
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
lookup t idx = [subst sub x | Match x sub <- matches t idx]

{-# INLINE matches #-}
matches :: TermOf a -> Frozen a -> [Match a]
matches t idx = matchesList (Term.singleton t) idx

freeze :: Index a -> Frozen a
freeze idx = Frozen $ \t -> find t idx []

find :: TermListOf a -> Index a -> [Match a] -> [Match a]
find t idx xs = aux t idx xs
  where
    aux !_ !_ _ | False = __
    aux _ Nil rest = rest
    aux t Index{size = size} rest
      | lenList t < size = rest
    aux Empty Index{here = here} rest = {-# SCC "try_here" #-} try here rest
    aux t (Singleton u x) rest
      | isJust (matchList u t) = {-# SCC "try_singleton" #-} try [x] rest
      | otherwise = rest
    aux t@(ConsSym (Fun (MkFun n) _) ts) Index{fun = fun, var = var} rest =
      case var of
        Nil -> aux ts (fun ! n) rest
        _   -> aux ts (fun ! n) (aux us var rest)
      where
        Cons _ us = t
    aux (Cons _ ts) Index{var = var} rest = aux ts var rest

    {-# INLINE try #-}
    try [] rest = rest
    try xs rest =
      {-# SCC "try" #-}
      [ Match x sub
      | Entry u x <- xs,
        sub <- maybeToList (matchList (Term.singleton u) t) ] ++
      rest

elems :: Index a -> [a]
elems Nil = []
elems (Singleton _ x) = [e_value x]
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
