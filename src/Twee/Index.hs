-- | A term index to accelerate matching.
-- An index is a multimap from terms to arbitrary values.
--
-- The type of query supported is: given a search term, find all keys such that
-- the search term is an instance of the key, and return the corresponding
-- values.

{-# LANGUAGE BangPatterns, RecordWildCards, OverloadedStrings, FlexibleContexts, CPP, TupleSections, TypeFamilies #-}
-- We get some bogus warnings because of pattern synonyms.
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
{-# OPTIONS_GHC -O2 -fmax-worker-args=100 #-}
#ifdef USE_LLVM
{-# OPTIONS_GHC -fllvm #-}
#endif
module Twee.Index(
  Index,
  empty,
  null,
  singleton,
  insert,
  delete,
  lookup,
  matches,
  elems,
  fromList,
  fromListWith) where

import Prelude hiding (null, lookup)
import Twee.Base hiding (var, fun, empty, singleton, prefix, funs, lookupList, lookup, at)
import qualified Twee.Term as Term
import Data.DynamicArray
import qualified Data.List as List
import Data.Numbered(Numbered)
import qualified Data.Numbered as Numbered
import qualified Data.IntMap.Strict as IntMap

-- The term index in this module is a _perfect discrimination tree_.
-- This is a trie whose keys are terms, represented as flat lists of symbols
-- (either functions or variables).
--
-- To insert a key-value pair into the discrimination tree, we do
-- ordinary trie insertion, but first canonicalising the key-value
-- pair so that variables are introduced in ascending order.
-- This canonicalisation reduces the size of the trie, but is also
-- needed for our particular implementation of lookup to work correctly
-- (specifically the extendBindings function below).
--
-- Lookup maintains a term list, which is initially the search term,
-- and a substitution. It proceeds down the trie, consuming bits of
-- the term list as it goes.
--
-- If the current trie node has an edge for a function symbol f, and the term at
-- the head of the term list is f(t1..tn), we can follow the f edge. We then
-- delete f from the term list, but keep t1..tn at the front of the term list.
-- (In other words we delete only the symbol f and not its arguments.)
--
-- If the current trie node has a variable edge x, we can follow that edge.
-- We remove the head term from the term list, as 'x' matches that
-- whole term. We then add the binding x->t to the substitution.
-- If the substitution already has a binding x->u with u/=t, we can't
-- follow the edge.
--
-- If the term list ever becomes empty, we have a match, and return
-- the substitution.
--
-- Often there are several edges we can follow (function symbol and
-- any number of variable edges), and in that case the algorithm uses
-- backtracking.

----------------------------------------------------------------------
-- The term index.
----------------------------------------------------------------------

-- | A term index: a multimap from @'Term' f@ to @a@.
data Index f a =
  -- A non-empty index.
  Index {
    -- The size of the smallest term in the index.
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
    -- List of variable edges indexed by variable number.
    -- Invariant: all edges present in the list are non-Nil.
    --
    -- Invariant: variables in terms are introduced in ascending
    -- order, with no gaps (i.e. if the term so far has the variables
    -- x1..xn, then the edges here must be drawn from x1...x{n+1}).
    var    :: {-# UNPACK #-} !(Numbered (Index f a)) } |
  -- An empty index.
  Nil
  deriving Show

instance Default (Index f a) where def = Nil

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

-- An index with one entry, taking a termlist instead of a term.
{-# INLINE singletonList #-}
singletonList :: TermList f -> a -> Index f a
singletonList t x = Index 0 t [x] newArray Numbered.empty

-- | Insert an entry into the index.
{-# SCC insert #-}
insert :: (Symbolic a, ConstantOf a ~ f) => Term f -> a -> Index f a -> Index f a
insert !t0 !x0 !idx = aux (Term.singleton t) idx
  where
    (!t, !x) = canonicalise (t0, x0) 
    aux t Nil = singletonList t x

    -- Non-empty prefix
    aux (ConsSym{hd = t, rest = ts}) idx@Index{prefix = ConsSym{hd = u, rest = us}}
      | t == u =
        addPrefix t (aux ts idx{prefix = us, size = size idx - 1})
    aux t idx@Index{prefix = Cons{}} = aux t (expand idx)

    -- Empty prefix
    aux Empty idx =
      idx { size = 0, here = x:here idx }
    aux t@ConsSym{hd = App f _, rest = u} idx =
      idx {
        size = lenList t `min` size idx,
        fun  = update (fun_id f) idx' (fun idx) }
      where
        idx' = aux u (fun idx ! fun_id f)
    aux t@ConsSym{hd = Var x, rest = u} idx =
      idx {
        size = lenList t `min` size idx,
        var  = Numbered.modify (var_id x) Nil (aux u) (var idx) }

    -- Add the root symbol of t to the prefix
    addPrefix t idx =
      idx{prefix = buildList (atom t `mappend` builder (prefix idx)),
          size = size idx + 1}
    atom (Var x) = Term.var x
    atom (App f _) = con f

-- | Delete an entry from the index.
{-# INLINEABLE delete #-}
{-# SCC delete #-}
delete :: (Symbolic a, ConstantOf a ~ f, Eq a) => Term f -> a -> Index f a -> Index f a
delete !t0 !x0 !idx = aux (Term.singleton t) idx
  where
    (!t, !x) = canonicalise (t0, x0) 
    aux _ Nil = Nil

    -- Non-empty prefix
    aux (ConsSym{rest = ts}) idx@Index{prefix = u@ConsSym{rest = us}} =
      -- The prefix must match, since the term ought to be in the index
      -- (which is checked in the Empty case below).
      case aux ts idx{prefix = us} of
        Nil -> Nil
        idx -> idx{prefix = u}
    aux _ idx@Index{prefix = Cons{}} = idx

    -- Empty prefix
    aux Empty idx
      | x `List.elem` here idx =
        idx { here = List.delete x (here idx) }
      | otherwise =
        error "deleted term not found in index"
    aux ConsSym{hd = App f _, rest = t} idx =
      idx { fun = update (fun_id f) (aux t (fun idx ! fun_id f)) (fun idx) }
    aux ConsSym{hd = Var x, rest = t} idx =
      idx { var = Numbered.filter (not . null) (Numbered.modify (var_id x) Nil (aux t) (var idx)) }

-- Helper for insert and delete:
-- Take an index with a prefix and pull out the first symbol of the prefix,
-- giving an index which doesn't start with a prefix.
{-# INLINE expand #-}
expand :: Index f a -> Index f a
expand idx@Index{size = size, prefix = ConsSym{hd = t, rest = ts}} =
  case t of
    Var x ->
      Index {
        size = size,
        prefix = Term.empty,
        here = [],
        fun = newArray,
        var = Numbered.fromList [(var_id x, idx { prefix = ts, size = size - 1 })] }
    App f _ ->
      Index {
        size = size,
        prefix = Term.empty,
        here = [],
        fun = update (fun_id f) idx { prefix = ts, size = size - 1 } newArray,
        var = Numbered.empty }

-- | Look up a term in the index. Finds all key-value such that the search term
-- is an instance of the key, and returns an instance of the the value which
-- makes the search term exactly equal to the key.
{-# INLINE lookup #-}
lookup :: (Has a b, Symbolic b, Has b (TermOf b)) => TermOf b -> Index (ConstantOf b) a -> [b]
lookup t idx = lookupList (Term.singleton t) idx

{-# INLINEABLE lookupList #-}
lookupList :: (Has a b, Symbolic b, Has b (TermOf b)) => TermListOf b -> Index (ConstantOf b) a -> [b]
lookupList t idx =
  [ subst sub (the x)
  | (sub, x) <- matchesList t idx ]

-- | Look up a term in the index. Like 'lookup', but returns the exact value
-- that was inserted into the index, not an instance. Also returns a substitution
-- which when applied to the value gives you the matching instance.
{-# INLINE matches #-}
matches :: Term f -> Index f a -> [(Subst f, a)]
matches t idx = matchesList (Term.singleton t) idx

{-# SCC matchesList #-}
matchesList :: TermList f -> Index f a -> [(Subst f, a)]
matchesList t idx =
  run (searchNode t emptyBindings idx Stop)

-- | Return all elements of the index.
elems :: Index f a -> [a]
elems Nil = []
elems idx =
  here idx ++
  concatMap elems (map snd (toList (fun idx))) ++
  concatMap elems (map snd (Numbered.toList (var idx)))

-- | Create an index from a list of items
fromList :: (Symbolic a, ConstantOf a ~ f) => [(Term f, a)] -> Index f a
fromList xs = foldr (uncurry insert) empty xs

-- | Create an index from a list of items
fromListWith :: (Symbolic a, ConstantOf a ~ f) => (a -> Term f) -> [a] -> Index f a
fromListWith f xs = foldr (\x -> insert (f x) x) empty xs

----------------------------------------------------------------------
-- Substitutions used internally during lookup.
----------------------------------------------------------------------

-- We represent a substitution as a list of terms, in
-- reverse order. That is, the substitution
-- {x1->t1, ..., xn->tn} is represented as
-- [xn, x{n-1}, ..., x1].
data Bindings f =
  Bindings
    {-# UNPACK #-} !Int -- the highest-numbered variable (n)
    !(BindList f)       -- the list of terms ([xn, ..., x1])

data BindList f = NilB | ConsB {-# UNPACK #-} !(TermList f) !(BindList f)

{-# INLINE emptyBindings #-}
-- An empty substitution
emptyBindings :: Bindings f
emptyBindings = Bindings (-1) NilB

{- INLINE extendBindings #-}
-- Extend a substitution.
-- The variable bound must either be present in the substitution,
-- or the current highest-numbered variable plus one.
extendBindings :: Var -> Term f -> Bindings f -> Maybe (Bindings f)
extendBindings (V x) t (Bindings n bs)
  | x > n = Just (Bindings (n+1) (ConsB (Term.singleton t) bs))
  | bs `at` (n - x) == Term.singleton t = Just (Bindings n bs)
  | otherwise = Nothing

at :: BindList f -> Int -> TermList f
at (ConsB t _) 0 = t
at (ConsB _ b) n = at b (n-1)

-- Convert a substitution into an ordinary Subst.
toSubst :: Bindings f -> Subst f
toSubst (Bindings n bs) =
  Subst (IntMap.fromDistinctAscList (loop n bs []))
  where
    loop !_ !_ !_ | False = undefined
    loop _ NilB sub = sub
    loop n (ConsB t bs) sub =
      loop (n-1) bs ((n, t):sub)

----------------------------------------------------------------------
-- Lookup.
----------------------------------------------------------------------

-- To get predictable performance, lookup uses an explicit stack
-- instead of a lazy list to control backtracking.
data Stack f a =
  -- We only ever backtrack into variable edges, not function edges.
  -- This stack frame represents a search of the variable edges of a
  -- node, starting at a particular variable.
  Frame {
    -- The term which should match the variable
    frame_term    :: {-# UNPACK #-} !(Term f),
    -- The remainder of the search term
    frame_terms   :: {-# UNPACK #-} !(TermList f),
    -- The current substitution
    frame_bind    :: {-# UNPACK #-} !(Bindings f),
    -- The list of variable edges
    frame_indexes :: {-# UNPACK #-} !(Numbered (Index f a)),
    -- The starting variable number
    frame_var     :: {-# UNPACK #-} !Int,
    -- The rest of the stack
    frame_rest    :: !(Stack f a) } |
  -- A stack frame which is used when we have found a matching node.
  Yield {
    -- The list of values found at this node
    yield_found  :: [a],
    -- The current substitution
    yield_binds  :: {-# UNPACK #-} !(Bindings f),
    -- The rest of the stack
    yield_rest   :: !(Stack f a) }
  -- End of stack.
  | Stop

-- Turn a stack into a list of results.
{-# SCC run #-}
run :: Stack f a -> [(Subst f, a)]
run Stop = []
run Frame{..} = run (searchVarsFrom frame_term frame_terms frame_bind frame_indexes frame_var frame_rest)
run Yield{..} = map (toSubst yield_binds,) yield_found ++ run yield_rest

-- Search starting with a given node and substitution.
{-# INLINE searchNode #-}
{-# SCC searchNode #-}
searchNode :: TermList f -> Bindings f -> Index f a -> Stack f a -> Stack f a
searchNode !_ !_ !_ !_ | False = undefined
searchNode t binds idx rest =
  case idx of
    Nil -> rest
    Index{..}
      | lenList t < size ->
        rest -- the search term is smaller than any in this index
      | otherwise ->
        searchLoop binds t prefix here fun var rest

-- The main work of 'search' goes on here.
-- It is carefully tweaked to generate nice code,
-- in particular casing on each term list exactly once.
searchLoop :: Bindings f -> TermList f -> TermList f -> [a] -> Array (Index f a) -> Numbered (Index f a) -> Stack f a -> Stack f a
searchLoop !_ !_ !_ _ !_ !_ _ | False = undefined
searchLoop binds search prefix here fun var rest =
  case search of
    ConsSym{hd = t, tl = ts, rest = ts1} ->
      case prefix of
        ConsSym{hd = u, tl = us, rest = us1} ->
          -- Check the search term against the prefix.
          case (t, u) of
            (_, Var x) ->
              case extendBindings x t binds of
                Just binds' ->
                  searchLoop binds' ts us here fun var rest
                Nothing ->
                  rest
            (App f _, App g _) | f == g ->
               -- Term and prefix start with same symbol, chop them off.
               searchLoop binds ts1 us1 here fun var rest
            _ ->
              -- Term and prefix don't match.
              rest
        _ ->
          -- We've exhausted the prefix, so let's descend into the tree.
          -- Seems to work better to explore the function node first.
          case t of
            App f _ ->
              case fun ! fun_id f of
                Nil ->
                  searchVars t ts binds var rest
                idx@Index{} ->
                  -- Avoid creating a frame unnecessarily.
                  case Numbered.size var of
                    0 -> searchNode ts1 binds idx rest
                    _ -> searchNode ts1 binds idx $! Frame t ts binds var 0 rest
            _ ->
              searchVars t ts binds var rest
    Empty ->
      case prefix of
        Empty ->
          -- The search term matches this node.
          case here of
            [] -> rest
            _ -> Yield here binds rest
        _ ->
          -- We've run out of search term - it doesn't match this node.
          rest

-- Search the variable-labelled edges of a node.
{-# INLINE searchVars #-}
searchVars :: Term f -> TermList f -> Bindings f -> Numbered (Index f a) -> Stack f a -> Stack f a
searchVars t ts bind var rest
  | Numbered.size var == 0 = rest
  | otherwise = searchVarsFrom t ts bind var 0 rest

-- Search the variable-labelled edges of a node,
-- starting with a particular variable.
searchVarsFrom :: Term f -> TermList f -> Bindings f -> Numbered (Index f a) -> Int -> Stack f a -> Stack f a
searchVarsFrom !_ !_ !_ !_ !_ _ | False = undefined
searchVarsFrom t ts binds var start rest
  | start >= Numbered.size var = rest
  | otherwise =
    let (x, idx) = var Numbered.! start in
    case extendBindings (V x) t binds of
      Just binds' ->
        searchNode ts binds' idx $!
        if start + 1 == Numbered.size var then rest
        else Frame t ts binds var (start+1) rest
      Nothing ->
        searchVarsFrom t ts binds var (start+1) rest

