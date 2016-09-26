-- Critical pairs.
{-# LANGUAGE BangPatterns, CPP #-}
module Twee.CP where

#include "errors.h"
import Twee.Base
import Twee.Rule
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe
import qualified Data.DList as DList

-- The set of positions at which a term can have critical overlaps.
newtype Positions f = Positions [Int]

positions :: Term f -> Positions f
positions t = Positions (aux 0 Set.empty (singleton t))
  where
    aux !_ !_ Empty = []
    aux n m (Cons (Var _) t) = aux (n+1) m t
    aux n m (ConsSym t@Fun{} u)
      | t `Set.member` m = aux (n+1) m u
      | otherwise = n:aux (n+1) (Set.insert t m) u

-- A critical overlap of one term with another.
data Overlap f =
  Overlap {
    overlap_top      :: {-# UNPACK #-} !(Term f),
    overlap_left     :: {-# UNPACK #-} !(Term f),
    overlap_right    :: {-# UNPACK #-} !(Term f),
    overlap_inner    :: {-# UNPACK #-} !(Term f) }

overlaps :: Positions f -> Rule f -> Rule f -> [Overlap f]
overlaps (Positions ns) (Rule _ outer outer') (Rule _ inner inner') =
  DList.toList $ go 0 ns (singleton outer)
  where
    go !_ _ !_ | False = __
    go _ [] _ = mzero
    go _ _ Empty = mzero
    go n (m:ms) (ConsSym t u)
      | m == n = here `mplus` go (n+1) ms u
      | otherwise = go (n+1) (m:ms) u
      where
        here = do
          sub <- DList.fromList (maybeToList (unifyTri inner t))
          let top = build (subst sub outer)
              left = build (subst sub outer')
              right = build (replacePositionSub (evalSubst sub) n (singleton inner') (singleton outer))
              inner_ = build (subst sub inner)
          return (Overlap top left right inner_)
