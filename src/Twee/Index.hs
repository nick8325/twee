-- Term indexing (perfect-ish discrimination trees).
{-# LANGUAGE BangPatterns, RecordWildCards, OverloadedStrings #-}
-- We get some bogus warnings because of pattern synonyms.
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
module Twee.Index(module Twee.Index, module Twee.Index.Lookup) where

import qualified Prelude
import Prelude hiding (filter, map, null)
import Twee.Base hiding (var, fun, empty, size, singleton, prefix, funs)
import qualified Twee.Term as Term
import Twee.Array
import qualified Data.List as List
import Twee.Profile
import Twee.Utils
import Twee.Index.Lookup

{-# INLINE null #-}
null :: Index f a -> Bool
null Nil = True
null _ = False

{-# INLINEABLE singleton #-}
singleton :: Term f -> a -> Index f a
singleton !t x = singletonEntry (key t) x

{-# INLINE singletonEntry #-}
singletonEntry :: TermList f -> a -> Index f a
singletonEntry t x = Index 0 t [x] newArray newVarIndex

{-# INLINE withPrefix #-}
withPrefix :: TermList f -> Index f a -> Index f a
withPrefix Empty idx = idx
withPrefix _ Nil = Nil
withPrefix t idx@Index{..} =
  idx{prefix = buildList (builder t `mappend` builder prefix)}

insert :: Term f -> a -> Index f a -> Index f a
insert !t x !idx = stamp "index insert" (aux (key t) idx)
  where
    aux t Nil = singletonEntry t x
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      withPrefix (Term.singleton t) (aux ts idx{prefix = us})
    aux t idx@Index{prefix = Cons{}} = aux t (expand idx)

    aux Empty idx =
      idx { size = 0, here = x:here idx }
    aux t@(ConsSym (Fun f _) u) idx =
      idx {
        size = lenList t `min` size idx,
        fun  = update (funid f) idx' (fun idx) }
      where
        idx' = aux u (fun idx ! funid f)
    aux t@(ConsSym (Var v) u) idx =
      idx {
        size = lenList t `min` size idx,
        var  = updateVarIndex v idx' (var idx) }
      where
        idx' = aux u (lookupVarIndex v (var idx))

{-# INLINE expand #-}
expand :: Index f a -> Index f a
expand idx@Index{prefix = ConsSym t ts} =
  case t of
    Var v ->
      Index (size idx + 1 + lenList ts) emptyTermList [] newArray
        (updateVarIndex v idx { prefix = ts } newVarIndex)
    Fun f _ ->
      Index (size idx + 1 + lenList ts) emptyTermList []
        (update (funid f) idx { prefix = ts } newArray) newVarIndex

key :: Term f -> TermList f
key t = buildList . aux . Term.singleton $ t
  where
    repeatedVars = [x | x <- usort (vars t), occVar x t > 1]

    aux Empty = mempty
    aux (ConsSym (Fun f _) t) =
      con f `mappend` aux t
    aux (ConsSym (Var x) t) =
      Term.var (
      case List.elemIndex x (take varIndexCapacity repeatedVars) of
         Nothing -> V 2
         Just n  -> V n) `mappend` aux t

{-# INLINEABLE delete #-}
delete :: Eq a => Term f -> a -> Index f a -> Index f a
delete !t x !idx = stamp "index delete" (aux (key t) idx)
  where
    aux _ Nil = Nil
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      withPrefix (Term.singleton t) (aux ts idx{prefix = us})
    aux _ idx@Index{prefix = Cons{}} = idx

    aux Empty idx =
      idx { here = List.delete x (here idx) }
    aux (ConsSym (Fun f _) t) idx =
      idx { fun = update (funid f) (aux t (fun idx ! funid f)) (fun idx) }
    aux (ConsSym (Var v) t) idx =
      idx { var = updateVarIndex v (aux t (lookupVarIndex v (var idx))) (var idx) }

{-# INLINEABLE elem #-}
elem :: Eq a => Term f -> a -> Index f a -> Bool
elem !t x !idx = aux (key t) idx
  where
    aux _ Nil = False
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      aux ts idx{prefix = us}
    aux _ Index{prefix = Cons{}} = False

    aux Empty idx = List.elem x (here idx)
    aux (ConsSym (Fun f _) t) idx =
      aux t (fun idx ! funid f)
    aux (ConsSym (Var v) t) idx =
      aux t (lookupVarIndex v (var idx))

newtype Frozen f a = Frozen { matchesList_ :: TermList f -> [a] }

matchesList :: TermList f -> Frozen f a -> [a]
matchesList t xs = stamp "index lookup" (matchesList_ xs t)

{-# INLINE matches #-}
matches :: Term f -> Frozen f a -> [a]
matches t idx = matchesList (Term.singleton t) idx

freeze :: Index f a -> Frozen f a
freeze idx = Frozen $ \t -> run (Frame emptySubst2 t idx Stop)

{-# NOINLINE run #-}
run :: Stack f a -> [a]
run Stop = []
run Frame{..} = run (stamp "index lookup (inner)" $ step frame_subst frame_term frame_index frame_rest)
run Yield{..} = stamp "index lookup (found)" $ yield_found ++ run yield_rest

elems :: Index f a -> [a]
elems Nil = []
elems idx =
  here idx ++
  concatMap elems (Prelude.map snd (toList (fun idx))) ++
  concatMap elems (varIndexElems (var idx))

{-# INLINE map #-}
map :: (a -> b) -> Frozen f a -> Frozen f b
map f (Frozen matches) = Frozen $ \t -> List.map f (matches t)

{-# INLINE filter #-}
filter :: (a -> Bool) -> Frozen f a -> Frozen f a
filter p (Frozen matches) = Frozen $ \t -> List.filter p (matches t)

{-# INLINE union #-}
union :: Frozen f a -> Frozen f a -> Frozen f a
union (Frozen f1) (Frozen f2) = Frozen $ \t -> f1 t ++ f2 t
