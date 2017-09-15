-- | A term index to accelerate matching.
-- An index is a multimap from terms to arbitrary values.
--
-- The type of query supported is: given a search term, find all keys such that
-- the search term is an instance of the key, and return the corresponding
-- values.

{-# LANGUAGE BangPatterns, RecordWildCards, OverloadedStrings, FlexibleContexts #-}
-- We get some bogus warnings because of pattern synonyms.
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
module Twee.Index(
  Index,
  empty,
  null,
  singleton,
  insert,
  delete,
  lookup,
  matches,
  approxMatches,
  elems) where

import qualified Prelude
import Prelude hiding (filter, map, null, lookup)
import Data.Maybe
import Twee.Base hiding (var, fun, empty, size, singleton, prefix, funs, lookupList, lookup)
import qualified Twee.Term as Term
import Data.DynamicArray
import qualified Data.List as List
import Twee.Utils
import Twee.Index.Lookup

-- Implementation note: the type definition and (performance-critical) core of
-- the lookup function are defined in Twee.Index.Lookup. This module defines the
-- remaining part of the API, which is not as performance-sensitive.

-- | An empty index.
{-# INLINE empty #-}
empty :: Index f a
empty = Nil

-- | Is the index empty?
{-# INLINE null #-}
null :: Index f a -> Bool
null Nil = True
null _ = False

-- | An index with one entry.
{-# INLINEABLE singleton #-}
singleton :: Term f -> a -> Index f a
singleton !t x = singletonEntry (key t) x

-- An index with one entry, giving the raw key.
{-# INLINE singletonEntry #-}
singletonEntry :: TermList f -> a -> Index f a
singletonEntry t x = Index 0 t [x] newArray newVarIndex

-- | Insert an entry into the index.
insert :: Term f -> a -> Index f a -> Index f a
insert !t x !idx = {-# SCC insert #-} aux (key t) idx
  where
    aux t Nil = singletonEntry t x
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      withPrefix (Term.singleton t) (aux ts idx{prefix = us})
    aux t idx@Index{prefix = Cons{}} = aux t (expand idx)

    aux Empty idx =
      idx { size = 0, here = x:here idx }
    aux t@(ConsSym (App f _) u) idx =
      idx {
        size = lenList t `min` size idx,
        fun  = update (fun_id f) idx' (fun idx) }
      where
        idx' = aux u (fun idx ! fun_id f)
    aux t@(ConsSym (Var v) u) idx =
      idx {
        size = lenList t `min` size idx,
        var  = updateVarIndex v idx' (var idx) }
      where
        idx' = aux u (lookupVarIndex v (var idx))

-- Add a prefix to an index.
-- Does not update the size field.
{-# INLINE withPrefix #-}
withPrefix :: TermList f -> Index f a -> Index f a
withPrefix Empty idx = idx
withPrefix _ Nil = Nil
withPrefix t idx@Index{..} =
  idx{prefix = buildList (builder t `mappend` builder prefix)}

-- Take an index with a prefix and pull out the first symbol of the prefix,
-- giving an index which doesn't start with a prefix.
{-# INLINE expand #-}
expand :: Index f a -> Index f a
expand idx@Index{size = size, prefix = ConsSym t ts} =
  case t of
    Var v ->
      Index {
        size = size,
        prefix = Term.empty,
        here = [],
        fun = newArray,
        var = updateVarIndex v idx { prefix = ts, size = size - 1 } newVarIndex }
    App f _ ->
      Index {
        size = size,
        prefix = Term.empty,
        here = [],
        fun = update (fun_id f) idx { prefix = ts, size = size - 1 } newArray,
        var = newVarIndex }

-- Compute the best key for a given term.
-- Maps the two most-repeated variables in the term to V 0 and V 1,
-- and all other variables to V 2.
key :: Term f -> TermList f
key t = buildList . aux . Term.singleton $ t
  where
    repeatedVars = [x | x <- usort (vars t), occVar x t > 1]

    aux Empty = mempty
    aux (ConsSym (App f _) t) =
      con f `mappend` aux t
    aux (ConsSym (Var x) t) =
      Term.var (
      case List.elemIndex x (take varIndexCapacity repeatedVars) of
         Nothing -> V varIndexCapacity
         Just n  -> V n) `mappend` aux t

-- | Delete an entry from the index.
{-# INLINEABLE delete #-}
delete :: Eq a => Term f -> a -> Index f a -> Index f a
delete !t x !idx = {-# SCC delete #-} aux (key t) idx
  where
    aux _ Nil = Nil
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      withPrefix (Term.singleton t) (aux ts idx{prefix = us})
    aux _ idx@Index{prefix = Cons{}} = idx

    aux Empty idx
      | x `List.elem` here idx =
        idx { here = List.delete x (here idx) }
      | otherwise =
        error "deleted term not found in index"
    aux (ConsSym (App f _) t) idx =
      idx { fun = update (fun_id f) (aux t (fun idx ! fun_id f)) (fun idx) }
    aux (ConsSym (Var v) t) idx =
      idx { var = updateVarIndex v (aux t (lookupVarIndex v (var idx))) (var idx) }

-- | Look up a term in the index. Finds all key-value such that the search term
-- is an instance of the key, and returns an instance of the the value which
-- makes the search term exactly equal to the key.
{-# INLINE lookup #-}
lookup :: (Has a b, Symbolic b, Has b (TermOf b)) => TermOf b -> Index (ConstantOf b) a -> [b]
lookup t idx = lookupList (Term.singleton t) idx

{-# INLINEABLE lookupList #-}
lookupList :: (Has a b, Symbolic b, Has b (TermOf b)) => TermListOf b -> Index (ConstantOf b) a -> [b]
lookupList t idx =
  [ subst sub x
  | x <- List.map the (approxMatchesList t idx),
    sub <- maybeToList (matchList (Term.singleton (the x)) t)]

-- | Look up a term in the index. Like 'lookup', but returns the exact value
-- that was inserted into the index, not an instance. Also returns a substitution
-- which when applied to the value gives you the matching instance.
{-# INLINE matches #-}
matches :: Has a (Term f) => Term f -> Index f a -> [(Subst f, a)]
matches t idx = matchesList (Term.singleton t) idx

{-# INLINEABLE matchesList #-}
matchesList :: Has a (Term f) => TermList f -> Index f a -> [(Subst f, a)]
matchesList t idx =
  [ (sub, x)
  | x <- approxMatchesList t idx,
    sub <- maybeToList (matchList (Term.singleton (the x)) t)]

-- | Look up a term in the index, possibly returning spurious extra results.
{-# INLINE approxMatches #-}
approxMatches :: Term f -> Index f a -> [a]
approxMatches t idx = approxMatchesList (Term.singleton t) idx

approxMatchesList :: TermList f -> Index f a -> [a]
approxMatchesList t idx =
  {-# SCC approxMatchesList #-}
  run (Frame emptySubst2 t idx Stop)

-- | Return all elements of the index.
elems :: Index f a -> [a]
elems Nil = []
elems idx =
  here idx ++
  concatMap elems (Prelude.map snd (toList (fun idx))) ++
  concatMap elems (varIndexElems (var idx))
