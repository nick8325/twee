-- Term indexing (perfect-ish discrimination trees).
-- This module contains the type definitions and lookup function.
-- We put lookup in a separate module because it needs to be compiled
-- with inlining switched up to max, and compiling the rest of the module
-- like that is too slow.
{-# LANGUAGE BangPatterns, RecordWildCards #-}
{-# OPTIONS_GHC -funfolding-creation-threshold=10000 -funfolding-use-threshold=10000 #-}
module Twee.Index.Lookup where

import Twee.Base hiding (var, fun, empty, size, singleton, prefix, funs)
import qualified Twee.Term as Term
import Twee.Term.Core(TermList(..))
import Twee.Array

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

{-# INLINE extend2 #-}
extend2 :: Var -> TermList f -> Subst2 f -> Maybe (Subst2 f)
extend2 (V 0) t (Subst2 _ 0 x y) = Just (Subst2 (low t) (high t) x y)
extend2 (V 0) t (Subst2 x y _ _) | t /= TermList x y (array t) = Nothing
extend2 (V 1) u (Subst2 x y _ 0) = Just (Subst2 x y (low u) (high u))
extend2 (V 1) u (Subst2 _ _ x y) | u /= TermList x y (array u) = Nothing
extend2 _ _ sub = Just sub

data Stack f a =
  Frame {
    frame_subst :: {-# UNPACK #-} !(Subst2 f),
    frame_term  :: {-# UNPACK #-} !(TermList f),
    frame_index :: !(Index f a),
    frame_rest  :: !(Stack f a) }
  | Yield {
    yield_found :: [a],
    yield_rest  :: !(Stack f a) }
  | Stop

step !_ !_ _ _ | False = undefined
step _ _ Nil rest = rest
step _ t Index{size = size, prefix = prefix} rest
  | lenList t < size + lenList prefix = rest
step sub t Index{..} rest = pref sub t prefix here fun var rest

pref !_ !_ !_ _ !_ !_ _ | False = undefined
pref _ Empty Empty [] _ _ rest = rest
pref _ Empty Empty here _ _ rest = Yield here rest
pref _ Empty _ _ _ _ _ = undefined -- implies lenList t < size + lenList prefix above
pref sub (Cons t ts) (Cons (Var x) us) here fun var rest =
  case extend2 x (Term.singleton t) sub of
    Nothing  -> rest
    Just sub -> pref sub ts us here fun var rest
pref sub (ConsSym (App f _) ts) (ConsSym (App g _) us) here fun var rest
  | f == g = pref sub ts us here fun var rest
pref _ _ (Cons _ _) _ _ _ rest = rest
pref sub t@(Cons u us) Empty _ fun var rest =
  tryFun sub v vs fun (tryVar sub u us var rest)
  where
    UnsafeConsSym v vs = t

    {-# INLINE tryFun #-}
    tryFun sub (App f _) ts fun rest =
      case fun ! fun_id f of
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
