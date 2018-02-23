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
import Prelude hiding (null, lookup)
import Data.Maybe
import Twee.Base hiding (var, fun, empty, size, singleton, prefix, funs, lookupList, lookup)
import qualified Twee.Term as Term
import Data.DynamicArray
import qualified Data.List as List

-- The term index in this module is an _imperfect discrimination tree_.
-- This is a trie whose keys are terms, represented as flat lists of symbols,
-- but where all variables have been replaced by a single don't-care variable '_'.
-- That is, the edges of the trie can be either function symbols or '_'.
-- To insert a key-value pair into the discrimination tree, we first replace all
-- variables in the key with '_', and then do ordinary trie insertion.
--
-- Lookup maintains a term list, which is initially the search term.
-- It proceeds down the trie, consuming bits of the term list as it goes.
--
-- If the current trie node has an edge for a function symbol f, and the term at
-- the head of the term list is f(t1..tn), we can follow the f edge. We then
-- delete f from the term list, but keep t1..tn at the front of the term list.
-- (In other words we delete only the symbol f and not its arguments.)
--
-- If the current trie node has an edge for '_', we can always follow that edge.
-- We then remove the head term from the term list, as the '_' represents a
-- variable that should match that whole term.
--
-- If the term list ever becomes empty, we have a possible match. We then
-- do matching on the values stored at the current node to see if they are
-- genuine matches.
--
-- Often there are two edges we can follow (function symbol and '_'), and in
-- that case the algorithm uses backtracking.

-- | A term index: a multimap from @'Term' f@ to @a@.
data Index f a =
  -- A non-empty index.
  Index {
    -- Size of smallest term in index.
    size   :: {-# UNPACK #-} !Int,
    -- When all keys in the index start with the same sequence of symbols, we
    -- compress them into this prefix; the "fun" and "var" fields below refer to
    -- the first symbol _after_ the prefix, and the "here" field contains values
    -- whose remaining key is exactly this prefix.
    prefix :: {-# UNPACK #-} !(TermList f),
    -- The values that are found at this node.
    here   :: [a],
    -- Function symbol edges.
    -- The array is indexed by function number.
    fun    :: {-# UNPACK #-} !(Array (Index f a)),
    -- Variable edge.
    var    :: !(Index f a) } |
  -- An empty index.
  Nil
  deriving Show

instance Default (Index f a) where def = Nil

-- To get predictable performance, the lookup function uses an explicit stack
-- instead of recursion to control backtracking.
data Stack f a =
  -- A normal stack frame: records the current index node and term.
  Frame {
    frame_term  :: {-# UNPACK #-} !(TermList f),
    frame_index :: !(Index f a),
    frame_rest  :: !(Stack f a) }
  -- A stack frame which is used when we have found a match.
  | Yield {
    yield_found :: [a],
    yield_rest  :: !(Stack f a) }
  -- End of stack.
  | Stop

-- Turn a stack into a list of results.
run :: Stack f a -> [a]
run Stop = []
run Frame{..} = run ({-# SCC run_inner #-} step frame_term frame_index frame_rest)
run Yield{..} = {-# SCC run_found #-} yield_found ++ run yield_rest

-- Execute a single stack frame.
{-# INLINE step #-}
step :: TermList f -> Index f a -> Stack f a -> Stack f a
step !_ _ _ | False = undefined
step t idx rest =
  case idx of
    Nil -> rest
    Index{..}
      | lenList t < size ->
        rest -- the search term is smaller than any in this index
      | otherwise ->
        pref t prefix here fun var rest

-- The main work of 'step' goes on here.
-- It is carefully tweaked to generate nice code,
-- including using UnsafeCons and only casing on each
-- term list exactly once.
pref :: TermList f -> TermList f -> [a] -> Array (Index f a) -> Index f a -> Stack f a -> Stack f a
pref !_ !_ _ !_ !_ _ | False = undefined
pref search prefix here fun var rest =
  case search of
    Empty ->
      case prefix of
        Empty ->
          -- The search term matches this node.
          case here of
            [] -> rest
            _ -> Yield here rest
        _ ->
          -- We've run out of search term - it doesn't match this node.
          rest
    UnsafeCons t ts ->
      case prefix of
        Cons u us ->
          -- Check the search term against the prefix.
          case (t, u) of
            (_, Var _) ->
              -- Prefix contains a variable - if there is a match, the
              -- variable will be bound to t.
              pref ts us here fun var rest
            (App f _, App g _) | f == g ->
              -- Term and prefix start with same symbol, chop them off.
               let
                 UnsafeConsSym _ ts' = search
                 UnsafeConsSym _ us' = prefix
               in pref ts' us' here fun var rest
            _ ->
              -- Term and prefix don't match.
              rest
        _ ->
          -- We've exhausted the prefix, so let's descend into the tree.
          -- Seems to work better to explore the function node first.
          let
            tryVar =
              case var of
                Nil -> rest
                Index{} -> Frame ts var rest
              where
                UnsafeCons _ ts = search

            tryFun =
              case t of
                App f _ ->
                  case fun ! fun_id f of
                    Nil -> tryVar
                    idx -> Frame ts idx $! tryVar
                _ ->
                  tryVar
              where
                UnsafeConsSym t ts = search
          in
            tryFun

-- | An empty index.
empty :: Index f a
empty = Nil

-- | Is the index empty?
null :: Index f a -> Bool
null Nil = True
null _ = False

-- | An index with one entry.
singleton :: Term f -> a -> Index f a
singleton !t x = singletonList (Term.singleton t) x

-- An index with one entry, giving a termlist instead of a term.
{-# INLINE singletonList #-}
singletonList :: TermList f -> a -> Index f a
singletonList t x = Index 0 t [x] newArray Nil

-- | Insert an entry into the index.
insert :: Term f -> a -> Index f a -> Index f a
insert !t x !idx = {-# SCC insert #-} aux (Term.singleton t) idx
  where
    aux t Nil = singletonList t x
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
    aux t@(ConsSym (Var _) u) idx =
      idx {
        size = lenList t `min` size idx,
        var  = aux u (var idx) }

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
    Var _ ->
      Index {
        size = size,
        prefix = Term.empty,
        here = [],
        fun = newArray,
        var = idx { prefix = ts, size = size - 1 } }
    App f _ ->
      Index {
        size = size,
        prefix = Term.empty,
        here = [],
        fun = update (fun_id f) idx { prefix = ts, size = size - 1 } newArray,
        var = Nil }

-- | Delete an entry from the index.
{-# INLINEABLE delete #-}
delete :: Eq a => Term f -> a -> Index f a -> Index f a
delete !t x !idx = {-# SCC delete #-} aux (Term.singleton t) idx
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
    aux (ConsSym (Var _) t) idx =
      idx { var = aux t (var idx) }

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
  run (Frame t idx Stop)

-- | Return all elements of the index.
elems :: Index f a -> [a]
elems Nil = []
elems idx =
  here idx ++
  concatMap elems (Prelude.map snd (toList (fun idx))) ++
  elems (var idx)
