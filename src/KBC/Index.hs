{-# LANGUAGE BangPatterns, CPP, UnboxedTuples, TypeFamilies #-}
-- Term indexing (perfect discrimination trees).
module KBC.Index where

#include "errors.h"
import qualified Prelude
import Prelude hiding (filter, map)
import KBC.Base hiding (var, fun, empty, vars, size)
import qualified KBC.Term as Term
import Control.Monad.ST.Strict
import GHC.ST
import KBC.Array hiding (null)
import qualified KBC.Array as Array
import Data.Maybe
import qualified Data.List as List
import Control.Monad

data Index a =
  Index {
    size :: {-# UNPACK #-} !Int,
    vars :: {-# UNPACK #-} !Int,
    here :: [a],
    fun  :: {-# UNPACK #-} !(Array (Index a)),
    var  :: {-# UNPACK #-} !(Array (Index a)) }
  deriving Show

updateHere :: ([a] -> [a]) -> Index a -> Index a
updateHere f idx = idx { here = f (here idx) }

updateVars :: Int -> Index a -> Index a
updateVars n idx = idx { vars = vars idx `max` n }

updateSize :: Int -> Index a -> Index a
updateSize n idx = idx { size = size idx `min` n }

updateFun ::
  Int -> (Index a -> Index a) -> Index a -> Index a
updateFun x f idx
  | KBC.Index.null idx' = idx { fun = update x Nothing (fun idx) }
  | otherwise = idx { fun = update x (Just idx') (fun idx) }
  where
    idx' = f (fromMaybe KBC.Index.empty (fun idx ! x))

updateVar ::
  Int -> (Index a -> Index a) -> Index a -> Index a
updateVar x f idx
  | KBC.Index.null idx' = idx { var = update x Nothing (var idx) }
  | otherwise = idx { var = update x (Just idx') (var idx) }
  where
    idx' = f (fromMaybe KBC.Index.empty (var idx ! x))

empty :: Index a
empty = Index maxBound 0 [] newArray newArray

null :: Index a -> Bool
null idx = Prelude.null (here idx) && Array.null (fun idx) && Array.null (var idx)

{-# INLINEABLE singleton #-}
singleton :: Symbolic a => a -> Index a
singleton x = insert x empty

{-# INLINEABLE insert #-}
insert :: Symbolic a => a -> Index a -> Index a
insert x0 !idx = aux t idx
  where
    aux Empty = updateSize 0 . updateVars n . updateHere (x:)
    aux t0@(ConsSym (Fun (MkFun f) _) t) = updateSize (lenList t0) . updateVars n . updateFun f (aux t)
    aux t0@(ConsSym (Var (MkVar x)) t) = updateSize (lenList t0) . updateVars n . updateVar x (aux t)
    n = boundList t
    x = canonicalise x0
    t = Term.singleton (term x)

{-# INLINEABLE delete #-}
delete :: (Eq a, Symbolic a) => a -> Index a -> Index a
delete x0 !idx = aux t idx
  where
    aux Empty = updateHere (List.delete x)
    aux (ConsSym (Fun (MkFun f) _) t) = updateFun f (aux t)
    aux (ConsSym (Var (MkVar x)) t) = updateVar x (aux t)
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

freeze :: Index a -> Frozen a
freeze !idx = {-# SCC freeze #-} Frozen $ \(!t) -> runST $ do
  msub <- newMutableSubst (vars idx)
  let
    loop !_ !_ _ | False = __
    loop Empty idx rest
      | Prelude.null (here idx) = rest
      | otherwise = do
        sub <- freezeSubst msub
        escape (Match (here idx) sub:) rest
    loop t idx rest | lenList t < size idx = rest
    loop t@(ConsSym (Fun f _) ts) idx rest =
      tryFun f ts (fun idx) (tryVar u us (var idx) rest)
      where
        Cons u us = t
    loop (Cons t ts) idx rest = tryVar t ts (var idx) rest

    tryFun (MkFun f) !t !fun rest =
      tryIn (fun ! f) rest (\idx -> loop t idx rest)
    tryVar !t !ts !var rest =
      aux 0
      where
        aux n
          | n >= arraySize var = rest
          | otherwise =
            tryIn (var ! n) (aux (n+1)) $ \idx -> do
              mu <- mutableLookupList msub (MkVar n)
              case mu of
                Nothing -> do
                  extend msub (MkVar n) t
                  loop ts idx (retract msub (MkVar n) >> aux (n+1))
                Just u
                  | Term.singleton t == u -> loop ts idx (aux (n+1))
                  | otherwise -> (aux (n+1))

    tryIn Nothing rest _ = rest
    tryIn (Just idx) rest f = f idx

  loop t idx (return [])

elems :: Index a -> [a]
elems idx =
  here idx ++
  concatMap elems (Prelude.map snd (toList (fun idx))) ++
  concatMap elems (Prelude.map snd (toList (var idx)))

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
