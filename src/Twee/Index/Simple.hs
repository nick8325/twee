-- Term indexing, a simple interface.
{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
module Twee.Index.Simple(module Twee.Index, module Twee.Index.Simple) where

import Prelude hiding (filter, map, null)
import Twee.Base hiding (var, fun, empty, size, singleton, prefix, funs)
import Data.Maybe
import qualified Twee.Index as Index
import Twee.Index(null, matchesList, matches, elems)

type Index a = Index.Index (ConstantOf a) a

{-# INLINE nil #-}
nil :: Index a
nil = Index.Nil

{-# INLINEABLE singleton #-}
singleton :: (Symbolic a, Has a (TermOf a)) => a -> Index a
singleton x = Index.singleton (the x) x

{-# INLINEABLE insert #-}
insert :: (Symbolic a, Has a (TermOf a)) => a -> Index a -> Index a
insert x idx = Index.insert (the x) x idx

{-# INLINEABLE delete #-}
delete :: (Eq a, Symbolic a, Has a (TermOf a)) => a -> Index a -> Index a
delete x idx = Index.delete (the x) x idx

{-# INLINEABLE elem #-}
elem :: (Eq a, Symbolic a, Has a (TermOf a)) => a -> Index a -> Bool
elem x idx = Index.elem (the x) x idx

{-# INLINEABLE lookup #-}
lookup :: (Symbolic a, Has a (TermOf a)) => TermOf a -> Index a -> [a]
lookup t idx =
  [subst sub x | (sub, x) <- matches t idx]
