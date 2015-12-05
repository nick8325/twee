-- Term indexing (perfect discrimination trees).
{-# LANGUAGE BangPatterns, CPP, UnboxedTuples, TypeFamilies, RecordWildCards #-}
-- We get some bogus warnings because of pattern synonyms.
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
{-# OPTIONS_GHC -funfolding-creation-threshold=1000000 -funfolding-use-threshold=1000000 #-}
module Twee.Index where

#include "errors.h"
import qualified Prelude
import Prelude hiding (filter, map, null)
import Twee.Base hiding (var, fun, empty, vars, size)
import qualified Twee.Term as Term
import Control.Monad.ST.Strict
import GHC.ST
import Twee.Array
import qualified Data.List as List
import Control.Monad

data Index a =
  Index {
    size :: {-# UNPACK #-} !Int,
    vars :: {-# UNPACK #-} !Int,
    here :: [a],
    fun  :: {-# UNPACK #-} !(Array (Index a)),
    var  :: !(Vars a) } |
  Singleton {
    vars  :: {-# UNPACK #-} !Int,
    key   :: {-# UNPACK #-} !(TermListOf a),
    value :: a } |
  Nil
  deriving Show

instance Default (Index a) where def = Nil

data Vars a = NilVars | ConsVars {-# UNPACK #-} !Var !(Index a) (Vars a)
  deriving Show

{-# INLINE cons #-}
cons :: Var -> Index a -> Vars a -> Vars a
cons _ Nil xs = xs
cons x idx xs = ConsVars x idx xs

{-# INLINE updateVar #-}
updateVar :: Var -> (Index a -> Index a) -> Vars a -> Vars a
updateVar x f NilVars = cons x (f Nil) NilVars
updateVar x f xs@(ConsVars y idx ys)
  | x <  y = cons x (f Nil) xs
  | x == y = ConsVars y (f idx) ys
  | x >  y = ConsVars y idx (updateVar x f ys)

{-# INLINE (!!!) #-}
(!!!) :: Vars a -> Var -> Index a
NilVars !!! _ = Nil
ConsVars x idx xs !!! y
  | x < y  = xs !!! y
  | x == y = idx
  | x > y  = Nil

varsToList :: Vars a -> [(Var, Index a)]
varsToList NilVars = []
varsToList (ConsVars x idx xs) = (x, idx):varsToList xs

{-# INLINE null #-}
null :: Index a -> Bool
null Nil = True
null _ = False

{-# INLINEABLE singleton #-}
singleton :: Symbolic a => a -> Index a
singleton x = Singleton (bound t) (Term.singleton t) x
  where
    t = term x

{-# INLINEABLE insert #-}
insert :: Symbolic a => a -> Index a -> Index a
insert x0 !idx = aux t idx
  where
    aux t Nil = Singleton (boundList t) t x
    aux t (Singleton _ u x) = aux t (expand u x)
    aux Empty idx@Index{..} = idx { size = 0, here = x:here }
    aux t@(ConsSym (Fun (MkFun f) _) u) idx =
      idx {
        size = lenList t `min` size idx,
        vars = vars idx `max` vars idx',
        fun  = update f idx' (fun idx) }
      where
        idx' = aux u (fun idx ! f)
    aux t@(ConsSym (Var v@(MkVar n)) u) idx =
      idx {
        size = lenList t `min` size idx,
        vars = vars idx `max` vars idx' `max` succ n,
        var  = updateVar v (const idx') (var idx) }
      where
        idx' = aux u (var idx !!! v)
    x = canonicalise x0
    t = Term.singleton (term x)

{-# INLINE expand #-}
expand :: TermListOf a -> a -> Index a
expand Empty x = Index 0 0 [x] newArray NilVars
expand (ConsSym s t) x =
  Index (1+lenList t) (n `max` m) [] fun var
  where
    (fun, var, MkVar m) =
      case s of
        Fun (MkFun f) _ ->
          (update f (Singleton n t x) newArray, NilVars, MkVar 0)
        Var v ->
          (newArray, cons v (Singleton n t x) NilVars, succ v)
    n = boundList t

{-# INLINEABLE delete #-}
delete :: (Eq a, Symbolic a) => a -> Index a -> Index a
delete x0 !idx = aux t idx
  where
    aux _ Nil = Nil
    aux t idx@(Singleton _ u _)
      | t == u    = Nil
      | otherwise = idx
    aux Empty idx = idx { here = List.delete x (here idx) }
    aux (ConsSym (Fun (MkFun f) _) t) idx =
      idx { fun = update f (aux t (fun idx ! f)) (fun idx) }
    aux (ConsSym (Var v) t) idx =
      idx { var = updateVar v (aux t) (var idx) }
    x = canonicalise x0
    t = Term.singleton (term x)

data Match a =
  Match {
    matchResult :: [a],
    matchSubst  :: SubstOf a }

newtype Frozen a = Frozen { matchesList_ :: TermListOf a -> [Match a] }

matchesList :: TermListOf a -> Frozen a -> [Match a]
matchesList = flip matchesList_

{-# INLINEABLE lookup #-}
lookup :: Symbolic a => TermOf a -> Frozen a -> [a]
lookup t idx = concat [Prelude.map (subst sub) xs | Match xs sub <- matches t idx]

{-# INLINE matches #-}
matches :: TermOf a -> Frozen a -> [Match a]
matches t idx = matchesList (Term.singleton t) idx

data Search a =
    Fail
  | Try {-# UNPACK #-} !(TermListOf a) (Index a) (Search a)
  | Single {-# UNPACK #-} !(SubstOf a) a (Search a)
  | Retract {-# UNPACK #-} !Var (Search a)
  | TryVar
    {-# UNPACK #-} !Var
    !(Index a)
    !(Vars a)
    {-# UNPACK #-} !(TermOf a)
    {-# UNPACK #-} !(TermListOf a)
    (Search a)

step :: MutableSubst s (ConstantOf a) -> Search a -> ST s (Maybe (Match a, Search a))
step !_ _ | False = __
step _ Fail = {-# SCC "step_fail" #-} return Nothing
step msub (Single sub x rest) = {-# SCC "step_single" #-} do
  sub0 <- unsafeFreezeSubst msub
  case substCompatible sub0 sub of
    True ->
      let !sub' = substUnion sub0 sub in
      return (Just (Match [x] sub', rest))
    False -> step msub rest
step msub (Try Empty Index{here = here} rest) = {-# SCC "step_base" #-} do
  sub <- freezeSubst msub
  return (Just (Match here sub, rest))
step msub (Try t@(ConsSym (Fun (MkFun n) _) ts) Index{fun = fun, var = var} rest) =
  {-# SCC "step_fun" #-}
  step msub (try ts (fun ! n) $! tryVar var u us rest)
  where
    Cons u us = t
step msub (Try (Cons t ts) Index{var = var} rest) =
  {-# SCC "step_var" #-}
  step msub (tryVar var t ts rest)
step msub (Retract n rest) = {-# SCC "step_retract" #-} do
  unsafeRetract msub n
  step msub rest
step msub (TryVar n idx var t ts rest) = {-# SCC "step_tryvar" #-} do
  mu <- mutableLookupList msub n
  case mu of
    Nothing -> {-# SCC "step_newvar" #-} do
      extendList msub n (Term.singleton t)
      step msub (try ts idx $! (Retract n $! tryVar var t ts rest))
    Just u
      | Term.singleton t == u ->
        {-# SCC "step_oldvar" #-}
        step msub (try ts idx $! tryVar var t ts rest)
      | otherwise ->
        {-# SCC "step_badvar" #-}
        step msub (tryVar var t ts rest)

{-# INLINE try #-}
try :: TermListOf a -> Index a -> Search a -> Search a
try !_ !_ _ | False = __
try _ Nil rest = rest
try t (Singleton _ u x) rest =
  case matchList u t of
    Nothing -> rest
    Just sub -> Single sub x rest
try Empty Index{here = []} rest = rest
try t Index{size = size} rest
  | lenList t < size = rest
try t idx rest = Try t idx rest

{-# INLINE tryVar #-}
tryVar :: Vars a -> TermOf a -> TermListOf a -> Search a -> Search a
tryVar NilVars !_ !_ rest = rest
tryVar (ConsVars n idx var) !t !ts rest = TryVar n idx var t ts rest

freeze :: Index a -> Frozen a
freeze Nil = Frozen $ \_ -> []
freeze idx = Frozen $ \(!t) -> runST $ do
  msub <- newMutableSubst (vars idx)
  let
    loop x = do
      r <- step msub x
      case r of
        Nothing -> return []
        Just (x, y) -> escape (x:) (loop y)
  loop (try t idx Fail)

elems :: Index a -> [a]
elems Nil = []
elems (Singleton _ _ x) = [x]
elems idx =
  here idx ++
  concatMap elems (Prelude.map snd (toList (fun idx))) ++
  concatMap elems (Prelude.map snd (varsToList (var idx)))

{-# INLINE map #-}
map :: (ConstantOf a ~ ConstantOf b) => (a -> b) -> Frozen a -> Frozen b
map f (Frozen matches) = Frozen $ \t -> [Match (Prelude.map f x) sub | Match x sub <- matches t]

{-# INLINE filter #-}
filter :: (a -> Bool) -> Frozen a -> Frozen a
filter p (Frozen matches) = Frozen $ \t -> do
  Match xs sub <- matches t
  let ys = [ x | x <- xs, p x ]
  guard (not (Prelude.null ys))
  return (Match ys sub)

{-# INLINE union #-}
union :: Frozen a -> Frozen a -> Frozen a
union (Frozen f1) (Frozen f2) = Frozen $ \t -> f1 t ++ f2 t

-- A rather scary little function for producing lazy values
-- in the strict ST monad. I hope it's sound...
-- Has a rather unsafeInterleaveST feel to it.
{-# INLINE escape #-}
escape :: (a -> b) -> ST s a -> ST s b
escape f (ST m) =
  ST $ \s ->
    (# s, f (case m s of (# _, x #) -> x) #)
