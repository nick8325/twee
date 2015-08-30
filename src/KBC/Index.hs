{-# LANGUAGE BangPatterns, CPP, RankNTypes, UnboxedTuples #-}
-- Term indexing (perfect discrimination trees).
{-# OPTIONS_GHC -funfolding-creation-threshold=1000000 -funfolding-use-threshold=100000 #-}
module KBC.Index where

#include "errors.h"
import Prelude hiding (filter)
import KBC.Term hiding (toList)
import qualified KBC.Term as Term
import Control.Monad.ST.Strict
import GHC.ST
import KBC.Array hiding (null)
import qualified KBC.Array as Array
import Data.Maybe
import qualified Data.List as List

data Index f a =
  Index {
    vars :: {-# UNPACK #-} !Int,
    here :: [a],
    fun  :: {-# UNPACK #-} !(Array (Index f a)),
    var  :: {-# UNPACK #-} !(Array (Index f a)) }
  deriving Show

updateHere :: ([a] -> [a]) -> Index f a -> Index f a
updateHere f idx = idx { here = f (here idx) }

updateVars :: Int -> Index f a -> Index f a
updateVars n idx = idx { vars = vars idx `max` n }

updateFun ::
  Int -> (Index f a -> Index f a) -> Index f a -> Index f a
updateFun x f idx
  | KBC.Index.null idx' = idx { fun = update x Nothing (fun idx) }
  | otherwise = idx { fun = update x (Just idx') (fun idx) }
  where
    idx' = f (fromMaybe KBC.Index.empty (fun idx ! x))

updateVar ::
  Int -> (Index f a -> Index f a) -> Index f a -> Index f a
updateVar x f idx
  | KBC.Index.null idx' = idx { var = update x Nothing (var idx) }
  | otherwise = idx { var = update x (Just idx') (var idx) }
  where
    idx' = f (fromMaybe KBC.Index.empty (var idx ! x))

empty :: Index f a
empty = Index 0 [] newArray newArray

null :: Index f a -> Bool
null idx = Prelude.null (here idx) && Array.null (fun idx) && Array.null (var idx)

{-# INLINEABLE singleton #-}
singleton :: Term f -> a -> Index f a
singleton t x = insert t x empty

{-# INLINE insert #-}
insert :: Term f -> a -> Index f a -> Index f a
insert t x idx = insertList (Term.singleton t) x idx

-- XXX need to canonicalise
{-# INLINEABLE insertList #-}
insertList :: TermList f -> a -> Index f a -> Index f a
insertList t x !idx = aux t idx
  where
    aux Empty = updateVars n . updateHere (x:)
    aux (ConsSym (Fun (MkFun f) _) t) = updateVars n . updateFun f (aux t)
    aux (ConsSym (Var (MkVar x)) t) = updateVars n . updateVar x (aux t)
    n = boundList t

{-# INLINE delete #-}
delete :: Eq a => Term f -> a -> Index f a -> Index f a
delete t x idx = deleteList (Term.singleton t) x idx

-- XXX really need to canonicalise
{-# INLINEABLE deleteList #-}
deleteList :: Eq a => TermList f -> a -> Index f a -> Index f a
deleteList t x !idx = aux t idx
  where
    aux Empty = updateHere (List.delete x)
    aux (ConsSym (Fun (MkFun f) _) t) = updateFun f (aux t)
    aux (ConsSym (Var (MkVar x)) t) = updateVar x (aux t)

{-
{-# INLINEABLE union #-}
union ::
  (Symbolic a, Ord a) =>
  Index a -> Index a -> Index a
union (Index here fun var) (Index here' fun' var') =
  Index
    (here ++ here')
    (IntMap.unionWith union fun fun')
    (IntMap.unionWith union var var')
-}
{-
{-# INLINEABLE lookup #-}
lookup ::
  (Symbolic a, Numbered (ConstantOf a), Eq (ConstantOf a)) =>
  TmOf a -> Index a -> [a]
lookup t idx = do
  (x, sub) <- matches t idx
  return (substf (evalSubst sub) x)
-}

data Match f a =
  Match {
    matchResult :: [a],
    matchSubst  :: Subst f }

{-# INLINE matches #-}
matches :: Term f -> Index f a -> [Match f a]
matches t idx = matchesList (Term.singleton t) idx

matchesList :: TermList f -> Index f a -> [Match f a]
matchesList !t !idx = runST $ do
  msub <- newMutableSubst t (vars idx)
  let
    loop !_ !_ | False = __
    loop Empty idx
      | Prelude.null (here idx) = return []
      | otherwise = do
        sub <- unsafeFreezeSubst msub
        return [Match (here idx) sub]
    loop t@(ConsSym (Fun f _) ts) idx =
      tryFun f ts (fun idx) (tryVar u us (var idx))
      where
        Cons u us = t
    loop (Cons t ts) idx = tryVar t ts (var idx)

    tryFun (MkFun f) !t !fun rest =
      tryIn (fun ! f) rest (loop t)
    tryVar !t !ts !var =
      aux 0
      where
        aux n
          | n >= arraySize var = return []
          | otherwise =
            tryIn (var ! n) (aux (n+1)) $ \idx -> do
              extend msub (MkVar n) t
              ms <- loop ts idx
              retract msub (MkVar n)
              return ms

    tryIn Nothing rest _ = rest
    tryIn (Just idx) rest f = do
      ms <- f idx
      case ms of
        [] -> rest
        m:ms -> escape ((m:) . (ms ++)) rest

  loop t idx

elems :: Index f a -> [a]
elems idx =
  here idx ++
  concatMap elems (map snd (toList (fun idx))) ++
  concatMap elems (map snd (toList (var idx)))

-- A rather scary little function for producing lazy values
-- in the strict ST monad. I hope it's sound...
-- Has a rather unsafeInterleaveST feel to it.
{-# INLINE escape #-}
escape :: (a -> b) -> ST s a -> ST s b
escape f (ST m) =
  ST $ \s ->
    (# s, f (case m s of (# _, x #) -> x) #)
