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
import Data.DynamicArray

-- There are two main approaches to term indexing for rewriting:
--   * A _perfect_ discrimination tree is a trie whose keys are terms,
--     represented as flat lists of symbols. To insert a key-value pair
--     into the discrimination tree we simply do trie insertion.
--
--     Lookup works by maintaining a term list, which is initially the search
--     term, and a substitution, which initially is empty. It proceeds down the
--     trie, consuming bits of the term list and extending the substitution.
--
--     If the trie node has an edge for a function symbol f, and the term at the
--     head of the term list is f(t1..tn), we can follow the f edge. We then
--     delete f from the term list, but keep t1..tn at the front of the term
--     list. (In other words we delete only the symbol f and not its arguments.)
--
--     If the trie node has an edge for a variable symbol X, we can try to
--     follow that edge. Supposing that t is the term at the head of the term
--     list, we extend the substitution with X := t and remove t from the term
--     list. If X was already bound to a term different from t, we can not
--     follow the X edge.
--
--     If the term list ever becomes empty, we have a match and the substitution.
--
--     Often there are several edges we can follow, and in that case the
--     algorithm uses backtracking.
--
--   * An _imperfect_ discrimination tree is similar, but in the keys we do not
--     remember which variable was which: we replace every variable in the key
--     with an underscore. Instead of many variable edges, the trie nodes have
--     a single underscore edge (besides all the function edges).
--     We then don't have to maintain a substitution during lookup (we are
--     always allowed to follow a variable edge), but at the end we have to
--     check if the match really was a match.
--
--     This is simpler to implement, and potentially does less backtracking as
--     the trie nodes have fewer edges. It also avoids having to maintain the
--     substitution during lookup, which is relatively expensive in twee where
--     substitutions are IntMaps. In practice, however, it gives many "false"
--     matches, and the extra overhead of rejecting those outweights the
--     benefits.
--
--     Note that we can only get false matches if the key has repeated variables.
--
-- The term index in this module is a hybrid of a perfect and imperfect
-- discrimination tree. When inserting a key-value pair, we pick out at most two
-- variables which we are going to keep track of; the rest are replaced by
-- underscores. At the moment we choose the two variables which are repeated
-- most often in the key. Let us call those variables X and Y.
--
-- Each node in the trie can then have three variable edges: X, Y and _.
-- During lookup we remember the value of X and Y (if we have bound them) and
-- check that we do not try to bind them to a different term, just as in a
-- perfect discrimination tree. At the end, we still have to check if our
-- matches are really matches. The hope is that this check will nearly always
-- succeed, and we get the performance of a perfect discrimination tree without
-- the difficulty of maintaining a substitution during lookup (we need only
-- remember two terms). This seems to be the case.

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
    -- Variable edges - X or Y or _ (see long description above).
    var    :: {-# UNPACK #-} !(VarIndex f a) } |
  -- An empty index.
  Nil
  deriving Show

instance Default (Index f a) where def = Nil

-- The three variable edges - X and Y and _.
data VarIndex f a =
  VarIndex {
    var0 :: !(Index f a), -- X (V 0)
    var1 :: !(Index f a), -- Y (V 1)
    hole :: !(Index f a)  -- _
  }
  deriving Show

-- An empty VarIndex.
{-# INLINE newVarIndex #-}
newVarIndex :: VarIndex f a
newVarIndex = VarIndex Nil Nil Nil

-- Follow an edge in a VarIndex.
{-# INLINE lookupVarIndex #-}
lookupVarIndex :: Var -> VarIndex f a -> Index f a
lookupVarIndex (V 0) vidx = var0 vidx
lookupVarIndex (V 1) vidx = var1 vidx
lookupVarIndex _ vidx = hole vidx

-- Modify an edge in a VarIndex.
{-# INLINE updateVarIndex #-}
updateVarIndex :: Var -> Index f a -> VarIndex f a -> VarIndex f a
updateVarIndex (V 0) idx vidx = vidx { var0 = idx }
updateVarIndex (V 1) idx vidx = vidx { var1 = idx }
updateVarIndex _ idx vidx = vidx { hole = idx }

-- Get all children of a VarIndex.
varIndexElems :: VarIndex f a -> [Index f a]
varIndexElems vidx = [var0 vidx, var1 vidx, hole vidx]

-- Convert a VarIndex into a list of (var number, index) pairs.
varIndexToList :: VarIndex f a -> [(Int, Index f a)]
varIndexToList vidx = [(0, var0 vidx), (1, var1 vidx), (2, hole vidx)]

-- The total number of variables we remember.
varIndexCapacity :: Int
varIndexCapacity = 2

-- A substitution which remembers only the values of X and Y.
-- We are naughty and exploit the fact that the search term is backed by a
-- single underlying array, and store only a pair of indices into that array
-- (the slice which holds the relevant term) instead of the full term.
data Subst2 f =
  Subst2
    -- x is bound to slice [lo..hi) of the search term's array.
    -- We represent an unbound variable by an empty slice.
    {-# UNPACK #-} !Int {-# UNPACK #-} !Int
    -- Ditto y
    {-# UNPACK #-} !Int {-# UNPACK #-} !Int

-- The empty substitution.
emptySubst2 :: Subst2 f
emptySubst2 = Subst2 0 0 0 0

-- Extend a substitution, checking for compatibility.
-- As noted above, the TermList must always share the same backing array.
{-# INLINE extend2 #-}
extend2 :: Var -> TermList f -> Subst2 f -> Maybe (Subst2 f)
extend2 (V 0) t (Subst2 _ 0 x y) = Just (Subst2 (low t) (high t) x y)
extend2 (V 0) t (Subst2 x y _ _) | t /= TermList x y (array t) = Nothing
extend2 (V 1) u (Subst2 x y _ 0) = Just (Subst2 x y (low u) (high u))
extend2 (V 1) u (Subst2 _ _ x y) | u /= TermList x y (array u) = Nothing
extend2 _ _ sub = Just sub

-- To get predictable performance, the lookup function uses an explicit stack
-- instead of recursion to control backtracking.
data Stack f a =
  -- A normal stack frame: records the current index node, term and substitution.
  Frame {
    frame_subst :: {-# UNPACK #-} !(Subst2 f),
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
{-# NOINLINE run #-}
run :: Stack f a -> [a]
run Stop = []
run Frame{..} = run ({-# SCC run_inner #-} step frame_subst frame_term frame_index frame_rest)
run Yield{..} = {-# SCC run_found #-} yield_found ++ run yield_rest

-- Execute a single stack frame.
step :: Subst2 f -> TermList f -> Index f a -> Stack f a -> Stack f a
step !_ !_ _ _ | False = undefined
step sub t idx rest =
  case idx of
    Nil -> rest
    Index{..}
      | lenList t < size ->
        rest -- the search term is smaller than any in this index
      | otherwise ->
        pref sub t prefix here fun var rest

-- The main work of 'step' goes on here.
pref :: Subst2 f -> TermList f -> TermList f -> [a] -> Array (Index f a) -> VarIndex f a -> Stack f a -> Stack f a
pref !_ !_ !_ _ !_ !_ _ | False = undefined
pref sub ts us here fun var rest =
  -- ts = search term
  -- us = prefix
  case (ts, us) of
    -- We've reached the end of the search term.
    (Empty, Empty) ->
      case here of
        [] -> rest
        _ -> Yield here rest
    -- Prefix contains a variable, bind it.
    (Cons t ts, Cons (Var x) us) ->
      case extend2 x (Term.singleton t) sub of
        Nothing  -> rest
        Just sub -> pref sub ts us here fun var rest
    -- Term and prefix start with same symbol, chop them off.
    (ConsSym (App f _) ts, ConsSym (App g _) us)
      | f == g ->
        pref sub ts us here fun var rest
    -- Term doesn't match prefix.
    (_, Cons _ _) ->
      rest
    -- At this point, we know ts /= Empty and us = Empty.
    -- We've exhausted the prefix, so let's descend into the tree.
    _ ->
      tryFun sub ts fun (tryVar sub ts var rest)
      where
        {-# INLINE tryFun #-}
        tryFun sub (UnsafeConsSym (App f _) ts) fun rest =
          case fun ! fun_id f of
            Nil -> rest
            idx -> Frame sub ts idx rest
        tryFun _ _ _ rest = rest

        {-# INLINE tryVar #-}
        tryVar sub (UnsafeCons t ts) var rest =
          foldr op rest (varIndexToList var)
          where
            op (x, idx@Index{}) rest
              | Just sub <- extend2 (V x) (Term.singleton t) sub =
                  Frame sub ts idx rest
            op _ rest = rest
