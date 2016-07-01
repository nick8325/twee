-- Term indexing, a simple interface.
{-# LANGUAGE TypeFamilies #-}
module Twee.Index.Simple(module Twee.Index, module Twee.Index.Simple) where

import qualified Prelude
import Prelude hiding (filter, map, null)
import Twee.Base hiding (var, fun, empty, size, singleton, prefix, funs)
import qualified Twee.Term as Term
import Twee.Array
import qualified Data.List as List
import Data.Maybe
import Twee.Profile
import Twee.Utils
import Control.Monad
import Twee.Term.Core(TermList(..))
import qualified Twee.Index as Index
import Twee.Index(null, matchesList, matches, freeze, elems, map, filter, union)

type Index a = Index.Index (ConstantOf a) a

{-# INLINE nil #-}
nil :: Index a
nil = Index.Nil

{-# INLINEABLE singleton #-}
singleton :: Singular a => a -> Index a
singleton x = Index.singleton (term x) x

{-# INLINEABLE insert #-}
insert :: Singular a => a -> Index a -> Index a
insert x idx = Index.insert (term x) x idx

{-# INLINEABLE delete #-}
delete :: (Eq a, Singular a) => a -> Index a -> Index a
delete x idx = Index.delete (term x) x idx

{-# INLINEABLE elem #-}
elem :: (Eq a, Singular a) => a -> Index a -> Bool
elem x idx = Index.elem (term x) x idx

type Frozen a = Index.Frozen (ConstantOf a) a

{-# INLINEABLE lookup #-}
lookup :: Singular a => TermOf a -> Frozen a -> [a]
lookup t idx =
  [subst sub x | x <- matches t idx, sub <- maybeToList (match (term x) t)]
