{-# LANGUAGE DeriveFunctor, FlexibleContexts, RankNTypes #-}
-- Term indexing (perfect discrimination trees).
module KBC.Index where

import Prelude hiding (filter)
import KBC.Base
import qualified Data.Map as Map
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict(IntMap)
import qualified Data.Rewriting.Substitution.Type as Subst
import qualified Data.Set as Set
import Data.Set(Set)

data Index a =
  Index {
    here :: Set a,
    fun  :: IntMap (Index a),
    var  :: IntMap (Index a) }
  deriving Show

updateHere :: Ord a => (Set a -> Set a) -> Index a -> Index a
updateHere f idx = idx { here = f (here idx) }

updateFun ::
  Int -> (Index a -> Index a) -> Index a -> Index a
updateFun x f idx
  | KBC.Index.null idx' = idx { fun = IntMap.delete x (fun idx) }
  | otherwise = idx { fun = IntMap.insert x idx' (fun idx) }
  where
    idx' = f (IntMap.findWithDefault KBC.Index.empty x (fun idx))

updateVar ::
  Int -> (Index a -> Index a) -> Index a -> Index a
updateVar x f idx
  | KBC.Index.null idx' = idx { var = IntMap.delete x (var idx) }
  | otherwise = idx { var = IntMap.insert x idx' (var idx) }
  where
    idx' = f (IntMap.findWithDefault KBC.Index.empty x (var idx))

empty :: Index a
empty = Index Set.empty IntMap.empty IntMap.empty

null :: Index a -> Bool
null idx = Set.null (here idx) && IntMap.null (fun idx) && IntMap.null (var idx)

mapMonotonic ::
  (a -> b) ->
  Index a -> Index b
mapMonotonic f (Index here fun var) =
  Index
    (Set.mapMonotonic f here)
    (fmap (mapMonotonic f) fun)
    (fmap (mapMonotonic f) var)

filter :: (a -> Bool) -> Index a -> Index a
filter p (Index here fun var) =
  Index
    (Set.filter p here)
    (fmap (filter p) fun)
    (fmap (filter p) var)

{-# INLINEABLE singleton #-}
singleton ::
  (Symbolic a, Numbered (ConstantOf a), Ord a) =>
  a -> Index a
singleton x = insert x empty

{-# INLINEABLE insert #-}
insert ::
  (Symbolic a, Numbered (ConstantOf a), Ord a) =>
  a -> Index a -> Index a
insert t = insertFlat (symbols (term u))
  where
    u = canonicalise t
    insertFlat [] = updateHere (Set.insert u)
    insertFlat (Left x:xs) = updateFun (number x) (insertFlat xs)
    insertFlat (Right x:xs) = updateVar (number x) (insertFlat xs)

{-# INLINEABLE delete #-}
delete ::
  (Symbolic a, Numbered (ConstantOf a), Ord a) =>
  a -> Index a -> Index a
delete t = deleteFlat (symbols (term u))
  where
    u = canonicalise t
    deleteFlat [] = updateHere (Set.delete u)
    deleteFlat (Left x:xs) = updateFun (number x) (deleteFlat xs)
    deleteFlat (Right x:xs) = updateVar (number x) (deleteFlat xs)

{-# INLINEABLE union #-}
union ::
  (Symbolic a, Ord a) =>
  Index a -> Index a -> Index a
union (Index here fun var) (Index here' fun' var') =
  Index
    (Set.union here here')
    (IntMap.unionWith union fun fun')
    (IntMap.unionWith union var var')

-- I want to define this as a CPS monad instead, but I run into
-- problems with inlining...
type Partial a b =
  (Subst (ConstantOf a) -> Index a -> b -> b) ->
   Subst (ConstantOf a) -> Index a -> b -> b

{-# INLINE yes #-}
yes :: Partial a b
yes ok sub idx err = ok sub idx err

{-# INLINE no #-}
no :: Partial a b
no _ _ _ err = err

{-# INLINE orElse #-}
orElse :: Partial a b -> Partial a b -> Partial a b
f `orElse` g = \ok sub idx err -> f ok sub idx (g ok sub idx err)

{-# INLINE andThen #-}
andThen :: Partial a b -> Partial a b -> Partial a b
f `andThen` g = \ok sub idx err -> f (\sub idx err -> g ok sub idx err) sub idx err

{-# INLINE withIndex #-}
withIndex :: Index a -> Partial a b -> Partial a b
withIndex idx f = \ok sub _ err -> f ok sub idx err

{-# INLINE inIndex #-}
inIndex :: (Index a -> Partial a b) -> Partial a b
inIndex f = \ok sub idx err -> f idx ok sub idx err

{-# INLINE partialToList #-}
partialToList ::
  (Subst (ConstantOf a) -> Index a -> [b]) ->
  Partial a [b] -> Index a -> [b]
partialToList f m idx =
  m (\sub idx rest -> f sub idx ++ rest) (Subst.fromMap Map.empty) idx []

{-# INLINEABLE lookup #-}
lookup ::
  (Symbolic a, Numbered (ConstantOf a), Eq (ConstantOf a)) =>
  TmOf a -> Index a -> [a]
lookup t idx = do
  (x, sub) <- matches t idx
  return (substf (evalSubst sub) x)

{-# INLINEABLE matches #-}
matches ::
  (Symbolic a, Numbered (ConstantOf a), Eq (ConstantOf a)) =>
  TmOf a -> Index a -> [(a, Subst (ConstantOf a))]
matches t idx = partialToList f (lookupPartial t) idx
  where
    f sub idx = do
      m <- Set.toList (here idx)
      return (m, sub)

    lookupPartial t = lookupFun t `orElse` lookupVar t

    {-# INLINE lookupVar #-}
    lookupVar t ok sub idx err =
      IntMap.foldrWithKey tryOne err (var idx)
      where
        {-# INLINE tryOne #-}
        tryOne x idx err =
          case Map.lookup (MkVar x) (Subst.toMap sub) of
            Just u | t == u -> ok sub idx err
            Just _ -> err
            Nothing ->
              let
                sub' = Subst.fromMap (Map.insert (MkVar x) t (Subst.toMap sub))
              in
                ok sub' idx err

    {-# INLINE lookupFun #-}
    lookupFun (Fun f ts) =
      inIndex $ \idx ->
        case IntMap.lookup (number f) (fun idx) of
          Nothing -> no
          Just idx ->
            let
              loop [] = yes
              loop (t:ts) = lookupPartial t `andThen` loop ts
            in
              withIndex idx (loop ts)
    lookupFun _ = no

elems :: Index a -> [a]
elems idx =
  Set.toList (here idx) ++
  concatMap elems (IntMap.elems (fun idx)) ++
  concatMap elems (IntMap.elems (var idx))
