-- Term indexing (perfect discrimination trees).
{-# LANGUAGE BangPatterns, CPP, TypeFamilies, RecordWildCards, OverloadedStrings #-}
-- We get some bogus warnings because of pattern synonyms.
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
{-# OPTIONS_GHC -O2 -funfolding-creation-threshold=10000 -funfolding-use-threshold=10000 -fllvm #-}
module Twee.Index where

#include "errors.h"
import qualified Prelude
import Prelude hiding (filter, map, null)
import Twee.Base hiding (var, fun, empty, size, singleton, prefix)
import qualified Twee.Term as Term
import Twee.Array
import qualified Data.List as List
import Data.Maybe
import Twee.Profile
import Twee.Utils
import Control.Monad

data Index a =
  Index {
    size   :: {-# UNPACK #-} !Int, -- size of smallest term, not including prefix
    prefix :: {-# UNPACK #-} !(TermListOf a),
    here   :: [Entry a],
    fun    :: {-# UNPACK #-} !(Array (Index a)),
    var    :: {-# UNPACK #-} !(VarIndex a) } |
  Nil
  deriving Show

instance Default (Index a) where def = Nil

data Entry a =
  Entry {
    e_key   :: {-# UNPACK #-} !(TermListOf a),
    e_value :: a }
  deriving (Eq, Show)

data VarIndex a =
  VarIndex {
    var0 :: !(Index a),
    var1 :: !(Index a),
    hole :: !(Index a) }
  deriving Show

{-# INLINE newVarIndex #-}
newVarIndex :: VarIndex a
newVarIndex = VarIndex Nil Nil Nil

{-# INLINE lookupVarIndex #-}
lookupVarIndex :: Var -> VarIndex a -> Index a
lookupVarIndex (MkVar 0) vidx = var0 vidx
lookupVarIndex (MkVar 1) vidx = var1 vidx
lookupVarIndex _ vidx = hole vidx

{-# INLINE updateVarIndex #-}
updateVarIndex :: Var -> Index a -> VarIndex a -> VarIndex a
updateVarIndex (MkVar 0) idx vidx = vidx { var0 = idx }
updateVarIndex (MkVar 1) idx vidx = vidx { var1 = idx }
updateVarIndex _ idx vidx = vidx { hole = idx }

varIndexElems :: VarIndex a -> [Index a]
varIndexElems vidx = [var0 vidx, var1 vidx, hole vidx]

varIndexToList :: VarIndex a -> [(Int, Index a)]
varIndexToList vidx = [(0, var0 vidx), (1, var1 vidx), (2, hole vidx)]

varIndexCapacity :: Int
varIndexCapacity = 2

data Subst2 f = Subst2 {-# UNPACK #-} !(TermList f) {-# UNPACK #-} !(TermList f)

emptySubst2 :: Subst2 a
emptySubst2 = Subst2 emptyTermList emptyTermList

extend2 :: Var -> TermList f -> Subst2 f -> Maybe (Subst2 f)
extend2 (MkVar 0) t (Subst2 Empty mu) = Just (Subst2 t mu)
extend2 (MkVar 0) t (Subst2 t' _) | t /= t' = Nothing
extend2 (MkVar 1) u (Subst2 mt Empty) = Just (Subst2 mt u)
extend2 (MkVar 1) u (Subst2 _ u') | u /= u' = Nothing
extend2 _ _ sub = Just sub

{-# INLINE null #-}
null :: Index a -> Bool
null Nil = True
null _ = False

{-# INLINEABLE singleton #-}
singleton :: Symbolic a => a -> Index a
singleton x = singletonEntry t (Entry t x)
  where
    t = Term.singleton (term x)

{-# INLINE singletonEntry #-}
singletonEntry :: TermListOf a -> Entry a -> Index a
singletonEntry t x = Index 0 t [x] newArray newVarIndex

{-# INLINE withPrefix #-}
withPrefix :: (ConstantOf a ~ f) => TermList f -> Index a -> Index a
withPrefix Empty idx = idx
withPrefix _ Nil = Nil
withPrefix t idx@Index{..} =
  idx{prefix = buildList (builder t `mappend` builder prefix)}

{-# INLINEABLE insert #-}
insert :: Symbolic a => a -> Index a -> Index a
insert x0 !idx = stamp "index insert" (aux (toKey (Term.singleton t)) idx)
  where
    aux t Nil = singletonEntry t e
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      withPrefix (Term.singleton t) (aux ts idx{prefix = us})
    aux t idx@Index{prefix = Cons{}} = aux t (expand idx)

    aux Empty idx =
      idx { size = 0, here = e:here idx }
    aux t@(ConsSym (Fun (MkFun f _) _) u) idx =
      idx {
        size = lenList t `min` size idx,
        fun  = update f idx' (fun idx) }
      where
        idx' = aux u (fun idx ! f)
    aux t@(ConsSym (Var v) u) idx =
      idx {
        size = lenList t `min` size idx,
        var  = updateVarIndex v idx' (var idx) }
      where
        idx' = aux u (lookupVarIndex v (var idx))
    t = term x
    x = indexCanonicalise x0
    e = Entry (Term.singleton t) x

{-# INLINE expand #-}
expand :: Index a -> Index a
expand idx@Index{prefix = ConsSym t ts} =
  case t of
    Var v ->
      Index (size idx + 1 + lenList ts) emptyTermList [] newArray
        (updateVarIndex v idx { prefix = ts } newVarIndex)
    Fun (MkFun f _) us ->
      Index (size idx + 1 + lenList ts) emptyTermList []
        (update f idx { prefix = ts } newArray) newVarIndex

toKey :: TermList a -> TermList a
toKey = buildList . aux
  where
    aux Empty = mempty
    aux (ConsSym (Fun f _) t) =
      con f `mappend` aux t
    aux (ConsSym (Var (MkVar x)) t) =
      Term.var (MkVar (x `min` varIndexCapacity)) `mappend` aux t

indexCanonicalise :: Symbolic a => a -> a
indexCanonicalise t = subst f u
  where
    u = subst (\(MkVar n) -> Term.var (MkVar (n+varIndexCapacity))) (canonicalise t)
    f x =
      Term.var $
      case List.elemIndex x (take varIndexCapacity repeatedVars) of
        Nothing -> x
        Just n  -> MkVar n
    repeatedVars = [x | x <- usort (vars u), occVar x u > 1]

{-# INLINEABLE delete #-}
delete :: (Eq a, Symbolic a) => a -> Index a -> Index a
delete x0 !idx = stamp "index delete" (aux (toKey (Term.singleton t)) idx)
  where
    aux _ Nil = Nil
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      withPrefix (Term.singleton t) (aux ts idx{prefix = us})
    aux _ idx@Index{prefix = Cons{}} = idx

    aux Empty idx =
      idx { here = List.delete e (here idx) }
    aux (ConsSym (Fun (MkFun f _) _) t) idx =
      idx { fun = update f (aux t (fun idx ! f)) (fun idx) }
    aux (ConsSym (Var v) t) idx =
      idx { var = updateVarIndex v (aux t (lookupVarIndex v (var idx))) (var idx) }
    t = term x
    x = canonicalise x0
    e = Entry (Term.singleton t) x

{-# INLINEABLE elem #-}
elem :: (Eq a, Symbolic a) => a -> Index a -> Bool
elem x0 !idx = aux (toKey (Term.singleton t)) idx
  where
    aux _ Nil = False
    aux (Cons t ts) idx@Index{prefix = Cons u us} | t == u =
      aux ts idx{prefix = us}
    aux _ idx@Index{prefix = Cons{}} = False

    aux Empty idx = List.elem e (here idx)
    aux (ConsSym (Fun (MkFun f _) _) t) idx =
      aux t (fun idx ! f)
    aux (ConsSym (Var v) t) idx =
      aux t (lookupVarIndex v (var idx))
    t = term x
    x = canonicalise x0
    e = Entry (Term.singleton t) x

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
freeze idx = Frozen $ \t -> find t idx

data Stack a =
  Frame {
    frame_subst :: {-# UNPACK #-} !(Subst2 (ConstantOf a)),
    frame_term  :: {-# UNPACK #-} !(TermListOf a),
    frame_index :: !(Index a),
    frame_rest  :: !(Stack a) }
  | Stop

find :: TermListOf a -> Index a -> [Match a]
find t idx = stamp "finding first match in index" (loop (initial t idx))
  where
    initial t idx = Frame emptySubst2 t idx Stop

    {-# INLINE loop #-}
    loop Stop = []
    loop Frame{..} = step frame_subst frame_term frame_index frame_rest

    {-# INLINE step #-}
    step !_ !_ _ _ | False = __
    step _ _ Nil rest = loop rest
    step _ t Index{size = size, prefix = prefix} rest
      | lenList t < size + lenList prefix = loop rest
    step sub t Index{..} rest =
      pref sub t prefix here fun var rest

    pref !_ !_ !_ _ !_ !_ _ | False = __
    pref _ Empty Empty [] _ _ rest = loop rest
    pref _ Empty Empty here _ _ rest =
      [ Match x sub
      | Entry u x <- here,
        sub <- maybeToList (matchList u t) ] ++
      loop rest
    pref _ Empty _ _ _ _ _ = __
    pref sub (Cons t ts) (Cons (Var x) us) here fun var rest =
      case extend2 x (Term.singleton t) sub of
        Nothing  -> loop rest
        Just sub -> pref sub ts us here fun var rest
    pref sub (ConsSym (Fun f _) ts) (ConsSym (Fun g _) us) here fun var rest
      | f == g = pref sub ts us here fun var rest
    pref _ _ (Cons _ _) _ _ _ rest = loop rest
    pref sub t@(ConsSym (Fun (MkFun n _) _) ts) Empty _ fun var rest =
      tryVar sub t var $
      case fun ! n of
        Nil -> rest
        idx -> Frame sub ts idx rest
    pref sub t@Cons{} Empty _ _ var rest = tryVar sub t var rest

    tryVar sub (UnsafeCons t ts) var rest =
      loop (foldr op rest (varIndexToList var))
      where
        op (x, idx@Index{}) rest
          | Just sub <- extend2 (MkVar x) (Term.singleton t) sub =
              Frame sub ts idx rest
        op _ rest = rest

elems :: Index a -> [a]
elems Nil = []
elems idx =
  List.map e_value (here idx) ++
  concatMap elems (Prelude.map snd (toList (fun idx))) ++
  concatMap elems (varIndexElems (var idx))

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
