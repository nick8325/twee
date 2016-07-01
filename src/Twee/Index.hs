-- Term indexing (perfect-ish discrimination trees).
{-# LANGUAGE BangPatterns, CPP, RecordWildCards, OverloadedStrings #-}
-- We get some bogus warnings because of pattern synonyms.
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
{-# OPTIONS_GHC -O2 -funfolding-creation-threshold=100000 -funfolding-use-threshold=100000 -fllvm #-}
module Twee.Index where

#include "errors.h"
import qualified Prelude
import Prelude hiding (filter, map, null)
import Twee.Base hiding (var, fun, empty, size, singleton, prefix, funs)
import qualified Twee.Term as Term
import Twee.Array
import qualified Data.List as List
import Twee.Profile
import Twee.Utils
import Twee.Term.Core(TermList(..))

data Index f a =
  Index {
    size   :: {-# UNPACK #-} !Int, -- size of smallest term, not including prefix
    prefix :: {-# UNPACK #-} !(TermList f),
    here   :: [a],
    fun    :: {-# UNPACK #-} !(Array (Index f a)),
    var    :: {-# UNPACK #-} !(VarIndex f a) } |
  Nil
  deriving Show

instance Default (Index f a) where def = Nil

data VarIndex f a =
  VarIndex {
    var0 :: !(Index f a),
    var1 :: !(Index f a),
    hole :: !(Index f a) }
  deriving Show

{-# INLINE newVarIndex #-}
newVarIndex :: VarIndex f a
newVarIndex = VarIndex Nil Nil Nil

{-# INLINE lookupVarIndex #-}
lookupVarIndex :: Var -> VarIndex f a -> Index f a
lookupVarIndex (V 0) vidx = var0 vidx
lookupVarIndex (V 1) vidx = var1 vidx
lookupVarIndex _ vidx = hole vidx

{-# INLINE updateVarIndex #-}
updateVarIndex :: Var -> Index f a -> VarIndex f a -> VarIndex f a
updateVarIndex (V 0) idx vidx = vidx { var0 = idx }
updateVarIndex (V 1) idx vidx = vidx { var1 = idx }
updateVarIndex _ idx vidx = vidx { hole = idx }

varIndexElems :: VarIndex f a -> [Index f a]
varIndexElems vidx = [var0 vidx, var1 vidx, hole vidx]

varIndexToList :: VarIndex f a -> [(Int, Index f a)]
varIndexToList vidx = [(0, var0 vidx), (1, var1 vidx), (2, hole vidx)]

varIndexCapacity :: Int
varIndexCapacity = 2

data Subst2 f = Subst2 {-# UNPACK #-} !Int {-# UNPACK #-} !Int {-# UNPACK #-} !Int {-# UNPACK #-} !Int

emptySubst2 :: Subst2 f
emptySubst2 = Subst2 0 0 0 0

extend2 :: Var -> TermList f -> Subst2 f -> Maybe (Subst2 f)
extend2 (V 0) t (Subst2 _ 0 x y) = Just (Subst2 (low t) (high t) x y)
extend2 (V 0) t (Subst2 x y _ _) | t /= TermList x y (array t) (funs t) = Nothing
extend2 (V 1) u (Subst2 x y _ 0) = Just (Subst2 x y (low u) (high u))
extend2 (V 1) u (Subst2 _ _ x y) | u /= TermList x y (array u) (funs u) = Nothing
extend2 _ _ sub = Just sub

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
matchesList = flip matchesList_

{-# INLINE matches #-}
matches :: Term f -> Frozen f a -> [a]
matches t idx = matchesList (Term.singleton t) idx

freeze :: Index f a -> Frozen f a
freeze idx = Frozen $ \t -> concat (find t idx)

data Stack f a =
  Frame {
    frame_subst :: {-# UNPACK #-} !(Subst2 f),
    frame_term  :: {-# UNPACK #-} !(TermList f),
    frame_index :: !(Index f a),
    frame_rest  :: !(Stack f a) }
  | Stop

{-# NOINLINE find #-}
find :: TermList f -> Index f a -> [[a]]
find t idx = stamp "finding first match in index" (loop (initial t idx))
  where
    initial t idx = Frame emptySubst2 t idx Stop

    {-# INLINE loop #-}
    loop Stop = []
    loop Frame{..} = step frame_subst frame_term frame_index frame_rest

    step !_ !_ _ _ | False = __
    step _ _ Nil rest = loop rest
    step _ t Index{size = size, prefix = prefix} rest
      | lenList t < size + lenList prefix = loop rest
    step sub t Index{..} rest =
      pref sub t prefix here fun var rest

    pref !_ !_ !_ _ !_ !_ _ | False = __
    pref _ Empty Empty [] _ _ rest = loop rest
    pref _ Empty Empty here _ _ rest = here:loop rest
    pref _ Empty _ _ _ _ _ = __
    pref sub (Cons t ts) (Cons (Var x) us) here fun var rest =
      case extend2 x (Term.singleton t) sub of
        Nothing  -> loop rest
        Just sub -> pref sub ts us here fun var rest
    pref sub (ConsSym (Fun f _) ts) (ConsSym (Fun g _) us) here fun var rest
      | f == g = pref sub ts us here fun var rest
    pref _ _ (Cons _ _) _ _ _ rest = loop rest
    pref sub t@(Cons u us) Empty _ fun var rest =
      loop $ tryFun sub v vs fun (tryVar sub u us var rest)
      where
        UnsafeConsSym v vs = t

    {-# INLINE tryFun #-}
    tryFun sub (Fun f _) ts fun rest =
      case fun ! funid f of
        Nil -> rest
        idx -> Frame sub ts idx rest
    tryFun _ _ _ _ rest = rest

    {-# INLINE tryVar #-}
    tryVar sub t ts var rest =
      foldr op rest (varIndexToList var)
      where
        op (x, idx@Index{}) rest
          | Just sub <- extend2 (V x) (Term.singleton t) sub =
              Frame sub ts idx rest
        op _ rest = rest

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
