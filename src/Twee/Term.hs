-- | Terms and substitutions, implemented using flatterms.

-- This module implements the usual term manipulation stuff
-- (matching, unification, etc.) on top of the primitives
-- in Twee.Term.Core.
{-# LANGUAGE BangPatterns, PatternSynonyms, ViewPatterns, TypeFamilies, OverloadedStrings, ScopedTypeVariables #-}
module Twee.Term(
  -- * Terms
  Term, pattern Var, pattern App,
  TermList, pattern Empty, pattern Cons, pattern ConsSym,
  pattern UnsafeCons, pattern UnsafeConsSym,
  Fun, fun, fun_id, fun_value, Var(..), 
  singleton,

  -- * Building terms
  Build(..),
  Builder,
  build, buildList,
  con, app, var,

  -- * Substitutions
  listSubstList, listSubst, foldSubst, allSubst, forMSubst_, substDomain,
  Substitution(..),
  subst, substSize, Subst(..),
  lookupList, extendList, retract, unsafeExtendList,
  substCompose, substCompatible, substUnion, idempotent, idempotentOn,
  close, canonicalise, emptySubst, flattenSubst,
  -- * Matching
  match, matchIn, matchList, matchListIn,
  TriangleSubst(..),
  -- * Unification
  unify, unifyList, unifyTri, unifyListTri,
  -- * Misc
  empty, children, unpack, lookup, extend, len,
  bound, boundList, occurs, subtermsList, subterms,
  properSubterms, isApp, isVar, isInstanceOf, isVariantOf,
  isSubtermOf, mapFun, mapFunList, replacePosition,
  replacePositionSub,
  positionToPath, pathToPosition,
  pattern F,
  (<<),
  at, lenList,
  isSubtermOfList) where

import Prelude hiding (lookup)
import Twee.Term.Core hiding (F)
import Data.List hiding (lookup, find)
import Data.Maybe
import Data.Monoid
import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as IntMap

--------------------------------------------------------------------------------
-- * A type class for builders
--------------------------------------------------------------------------------

-- | A type that can be turned into a 'Builder' of termlists.
--
-- Has instances for most reasonable things, including lists. The main
-- missing instance is for 'Var'; you will need to use 'var' instead.
class Build a where
  -- | The underlying type of function symbols.
  type BuildFun a
  -- | Turn the thing into a 'Builder'.
  builder :: a -> Builder (BuildFun a)

instance Build (Builder f) where
  type BuildFun (Builder f) = f
  builder = id

instance Build (Term f) where
  type BuildFun (Term f) = f
  builder = emitTermList . singleton

instance Build (TermList f) where
  type BuildFun (TermList f) = f
  builder = emitTermList

instance Build a => Build [a] where
  type BuildFun [a] = BuildFun a
  {-# INLINE builder #-}
  builder = mconcat . map builder

-- | Build a term. The given builder must produce exactly one term.
{-# INLINE build #-}
build :: Build a => a -> Term (BuildFun a)
build x =
  case buildList x of
    Cons t Empty -> t

-- | Build a termlist.
{-# INLINE buildList #-}
buildList :: Build a => a -> TermList (BuildFun a)
buildList x = {-# SCC buildList #-} buildTermList (builder x)

-- | Build a constant (a function with no arguments).
{-# INLINE con #-}
con :: Fun f -> Builder f
con x = emitApp x mempty

-- | Build a function application.
{-# INLINE app #-}
app :: Build a => Fun (BuildFun a) -> a -> Builder (BuildFun a)
app f ts = emitApp f (builder ts)

-- | Build a variable.
var :: Var -> Builder f
var = emitVar

--------------------------------------------------------------------------------
-- Functions for substitutions.
--------------------------------------------------------------------------------

{-# INLINE listSubstList #-}
listSubstList :: Subst f -> [(Var, TermList f)]
listSubstList (Subst sub) = [(V x, t) | (x, t) <- IntMap.toList sub]

{-# INLINE listSubst #-}
listSubst :: Subst f -> [(Var, Term f)]
listSubst sub = [(x, t) | (x, Cons t Empty) <- listSubstList sub]

{-# INLINE foldSubst #-}
foldSubst :: (Var -> TermList f -> b -> b) -> b -> Subst f -> b
foldSubst op e !sub = foldr (uncurry op) e (listSubstList sub)

{-# INLINE allSubst #-}
allSubst :: (Var -> TermList f -> Bool) -> Subst f -> Bool
allSubst p = foldSubst (\x t y -> p x t && y) True

{-# INLINE forMSubst_ #-}
forMSubst_ :: Monad m => Subst f -> (Var -> TermList f -> m ()) -> m ()
forMSubst_ sub f = foldSubst (\x t m -> do { f x t; m }) (return ()) sub

{-# INLINE substDomain #-}
substDomain :: Subst f -> [Var]
substDomain (Subst sub) = map V (IntMap.keys sub)

--------------------------------------------------------------------------------
-- Substitution.
--------------------------------------------------------------------------------

class Substitution s where
  type SubstFun s
  evalSubst :: s -> Var -> Builder (SubstFun s)

  {-# INLINE substList #-}
  substList :: s -> TermList (SubstFun s) -> Builder (SubstFun s)
  substList sub ts = aux ts
    where
      aux Empty = mempty
      aux (Cons (Var x) ts) = evalSubst sub x <> aux ts
      aux (Cons (App f ts) us) = app f (aux ts) <> aux us

instance (Build a, v ~ Var) => Substitution (v -> a) where
  type SubstFun (v -> a) = BuildFun a

  {-# INLINE evalSubst #-}
  evalSubst sub x = builder (sub x)

instance Substitution (Subst f) where
  type SubstFun (Subst f) = f

  {-# INLINE evalSubst #-}
  evalSubst sub x =
    case lookupList x sub of
      Nothing -> var x
      Just ts -> builder ts

{-# INLINE subst #-}
subst :: Substitution s => s -> Term (SubstFun s) -> Builder (SubstFun s)
subst sub t = substList sub (singleton t)

newtype Subst f =
  Subst {
    unSubst :: IntMap (TermList f) }
  deriving Eq

-- | Return the highest-number variable in a substitution plus 1.
{-# INLINE substSize #-}
substSize :: Subst f -> Int
substSize (Subst sub)
  | IntMap.null sub = 0
  | otherwise = fst (IntMap.findMax sub) + 1

-- | Look up a variable in a substitution, returning a termlist.
{-# INLINE lookupList #-}
lookupList :: Var -> Subst f -> Maybe (TermList f)
lookupList x (Subst sub) = IntMap.lookup (var_id x) sub

-- | Add a new binding to a substitution, giving a termlist.
{-# INLINE extendList #-}
extendList :: Var -> TermList f -> Subst f -> Maybe (Subst f)
extendList x !t (Subst sub) =
  case IntMap.lookup (var_id x) sub of
    Nothing -> Just $! Subst (IntMap.insert (var_id x) t sub)
    Just u
      | t == u    -> Just (Subst sub)
      | otherwise -> Nothing

-- | Remove a binding from a substitution.
{-# INLINE retract #-}
retract :: Var -> Subst f -> Subst f
retract x (Subst sub) = Subst (IntMap.delete (var_id x) sub)

-- | Add a new binding to a substitution.
-- Overwrites any existing binding.
{-# INLINE unsafeExtendList #-}
unsafeExtendList :: Var -> TermList f -> Subst f -> Subst f
unsafeExtendList x !t (Subst sub) = Subst (IntMap.insert (var_id x) t sub)

-- | Compose two substitutions.
substCompose :: Substitution s => Subst (SubstFun s) -> s -> Subst (SubstFun s)
substCompose (Subst !sub1) !sub2 =
  Subst (IntMap.map (buildList . substList sub2) sub1)

-- | Check if two substitutions are compatible.
substCompatible :: Subst f -> Subst f -> Bool
substCompatible (Subst !sub1) (Subst !sub2) =
  IntMap.null (IntMap.mergeWithKey f g h sub1 sub2)
  where
    f _ t u
      | t == u = Nothing
      | otherwise = Just t
    g _ = IntMap.empty
    h _ = IntMap.empty

-- | Take the union of two substitutions.
-- The substitutions must be compatible, which is not checked.
substUnion :: Subst f -> Subst f -> Subst f
substUnion (Subst !sub1) (Subst !sub2) =
  Subst (IntMap.union sub1 sub2)

-- | Check if a substitution is idempotent.
{-# INLINE idempotent #-}
idempotent :: Subst f -> Bool
idempotent !sub = allSubst (\_ t -> sub `idempotentOn` t) sub

-- | Check if a substitution has no effect on a given term.
{-# INLINE idempotentOn #-}
idempotentOn :: Subst f -> TermList f -> Bool
idempotentOn !sub = aux
  where
    aux Empty = True
    aux (ConsSym App{} t) = aux t
    aux (Cons (Var x) t) = isNothing (lookupList x sub) && aux t

-- | Iterate a substitution to make it idempotent.
close :: TriangleSubst f -> Subst f
close (Triangle sub)
  | idempotent sub = sub
  | otherwise      = close (Triangle (substCompose sub sub))

-- | Return a substitution for canonicalising a list of terms.
canonicalise :: [TermList f] -> Subst f
canonicalise [] = emptySubst
canonicalise (t:ts) = loop emptySubst vars t ts
  where
    n = maximum (V 0:map boundList (t:ts))
    vars =
      buildTermList $
        mconcat [emitVar x | x <- [V 0..n]]

    loop !_ !_ !_ !_ | False = undefined
    loop sub _ Empty [] = sub
    loop sub vs Empty (t:ts) = loop sub vs t ts
    loop sub vs (ConsSym App{} t) ts = loop sub vs t ts
    loop sub vs0@(Cons v vs) (Cons (Var x) t) ts =
      case extend x v sub of
        Just sub -> loop sub vs  t ts
        Nothing  -> loop sub vs0 t ts

-- | The empty substitution.
{-# NOINLINE emptySubst #-}
emptySubst = Subst IntMap.empty

-- | Construct a substitution from a list.
flattenSubst :: [(Var, Term f)] -> Maybe (Subst f)
flattenSubst sub = matchList pat t
  where
    pat = buildList (map (var . fst) sub)
    t   = buildList (map snd sub)

--------------------------------------------------------------------------------
-- Matching.
--------------------------------------------------------------------------------

-- | @'match' pat t@ matches the term @t@ against the pattern @pat@.
{-# INLINE match #-}
match :: Term f -> Term f -> Maybe (Subst f)
match pat t = matchList (singleton pat) (singleton t)

-- | A variant of 'match' which extends an existing substitution.
{-# INLINE matchIn #-}
matchIn :: Subst f -> Term f -> Term f -> Maybe (Subst f)
matchIn sub pat t = matchListIn sub (singleton pat) (singleton t)

-- | A variant of 'match' which works on termlists.
{-# INLINE matchList #-}
matchList :: TermList f -> TermList f -> Maybe (Subst f)
matchList pat t = matchListIn emptySubst pat t

-- | A variant of 'match' which works on termlists
-- and extends an existing substitution.
matchListIn :: Subst f -> TermList f -> TermList f -> Maybe (Subst f)
matchListIn !sub !pat !t
  | lenList t < lenList pat = Nothing
  | otherwise =
    let loop !_ !_ !_ | False = undefined
        loop sub Empty Empty = Just sub
        loop sub (ConsSym (App f _) pat) (ConsSym (App g _) t)
          | f == g = loop sub pat t
        loop sub (Cons (Var x) pat) (Cons t u) = do
          sub <- extend x t sub
          loop sub pat u
        loop _ _ _ = Nothing
    in {-# SCC match #-} loop sub pat t

--------------------------------------------------------------------------------
-- Unification.
--------------------------------------------------------------------------------

-- | A triangle substitution is one in which variables can be defined in terms
-- of each other, though not in a circular way.
--
-- The main use of triangle substitutions is in unification; 'unifyTri' returns
-- one. A triangle substitution can be converted to an ordinary substitution
-- with 'close', or used directly using its 'Substitution' instance.
newtype TriangleSubst f = Triangle { unTriangle :: Subst f }
  deriving Show

instance Substitution (TriangleSubst f) where
  type SubstFun (TriangleSubst f) = f

  {-# INLINE evalSubst #-}
  evalSubst (Triangle sub) x =
    case lookupList x sub of
      Nothing  -> var x
      Just ts  -> substList (Triangle sub) ts

  -- Redefine substList to get better inlining behaviour
  {-# INLINE substList #-}
  substList (Triangle sub) ts = aux ts
    where
      aux Empty = mempty
      aux (Cons (Var x) ts) = auxVar x <> aux ts
      aux (Cons (App f ts) us) = app f (aux ts) <> aux us

      auxVar x =
        case lookupList x sub of
          Nothing -> var x
          Just ts -> aux ts

-- | Unify two terms.
unify :: Term f -> Term f -> Maybe (Subst f)
unify t u = unifyList (singleton t) (singleton u)

-- | Unify two termlists.
unifyList :: TermList f -> TermList f -> Maybe (Subst f)
unifyList t u = do
  sub <- unifyListTri t u
  -- Not strict so that isJust (unify t u) doesn't force the substitution
  return (close sub)

-- | Unify two terms, returning a triangle substitution.
unifyTri :: Term f -> Term f -> Maybe (TriangleSubst f)
unifyTri t u = unifyListTri (singleton t) (singleton u)

-- | Unify two termlists, returning a triangle substitution.
unifyListTri :: TermList f -> TermList f -> Maybe (TriangleSubst f)
unifyListTri !t !u = fmap Triangle ({-# SCC unify #-} loop emptySubst t u)
  where
    loop !_ !_ !_ | False = undefined
    loop sub Empty Empty = Just sub
    loop sub (ConsSym (App f _) t) (ConsSym (App g _) u)
      | f == g = loop sub t u
    loop sub (Cons (Var x) t) (Cons u v) = do
      sub <- var sub x u
      loop sub t v
    loop sub (Cons t u) (Cons (Var x) v) = do
      sub <- var sub x t
      loop sub u v
    loop _ _ _ = Nothing

    var sub x t =
      case lookupList x sub of
        Just u -> loop sub u (singleton t)
        Nothing -> var1 sub x t

    var1 sub x t@(Var y)
      | x == y = return sub
      | otherwise =
        case lookup y sub of
          Just t  -> var1 sub x t
          Nothing -> extend x t sub

    var1 sub x t = do
      occurs sub x (singleton t)
      extend x t sub

    occurs !_ !_ Empty = Just ()
    occurs sub x (ConsSym App{} t) = occurs sub x t
    occurs sub x (ConsSym (Var y) t)
      | x == y = Nothing
      | otherwise = do
          occurs sub x t
          case lookupList y sub of
            Nothing -> Just ()
            Just u  -> occurs sub x u

--------------------------------------------------------------------------------
-- Miscellaneous stuff.
--------------------------------------------------------------------------------

-- | The empty termlist.
{-# NOINLINE empty #-}
empty :: forall f. TermList f
empty = buildList (mempty :: Builder f)

-- | Get the children (direct subterms) of a term.
children :: Term f -> TermList f
children t =
  case singleton t of
    UnsafeConsSym _ ts -> ts

-- | Convert a termlist into an ordinary list of terms.
unpack :: TermList f -> [Term f]
unpack t = unfoldr op t
  where
    op Empty = Nothing
    op (Cons t ts) = Just (t, ts)

instance Show (Term f) where
  show (Var x) = show x
  show (App f Empty) = show f
  show (App f ts) = show f ++ "(" ++ intercalate "," (map show (unpack ts)) ++ ")"

instance Show (TermList f) where
  show = show . unpack

instance Show (Subst f) where
  show subst =
    show
      [ (i, t)
      | i <- [0..substSize subst-1],
        Just t <- [lookup (V i) subst] ]

-- | Look up a variable in a substitution.
{-# INLINE lookup #-}
lookup :: Var -> Subst f -> Maybe (Term f)
lookup x s = do
  Cons t Empty <- lookupList x s
  return t

-- | Add a new binding to a substitution.
{-# INLINE extend #-}
extend :: Var -> Term f -> Subst f -> Maybe (Subst f)
extend x t sub = extendList x (singleton t) sub

-- | Find the length of a term.
{-# INLINE len #-}
len :: Term f -> Int
len = lenList . singleton

-- | Return the highest-numbered variable in a term plus 1.
{-# INLINE bound #-}
bound :: Term f -> Var
bound t = boundList (singleton t)

-- | Return the highest-numbered variable in a termlist plus 1.
{-# INLINE boundList #-}
boundList :: TermList f -> Var
boundList t = aux (V 0) t
  where
    aux n Empty = n
    aux n (ConsSym App{} t) = aux n t
    aux n (ConsSym (Var x) t)
      | x >= n = aux (succ x) t
      | otherwise = aux n t

-- | Check if a variable occurs in a term.
{-# INLINE occurs #-}
occurs :: Var -> Term f -> Bool
occurs x t = occursList x (singleton t)

-- | Find all subterms of a termlist.
{-# INLINE subtermsList #-}
subtermsList :: TermList f -> [Term f]
subtermsList t = unfoldr op t
  where
    op Empty = Nothing
    op (ConsSym t u) = Just (t, u)

-- | Find all subterms of a term.
{-# INLINE subterms #-}
subterms :: Term f -> [Term f]
subterms = subtermsList . singleton

-- | Find all proper subterms of a term.
{-# INLINE properSubterms #-}
properSubterms :: Term f -> [Term f]
properSubterms = subtermsList . children

-- | Check if a term is a function application.
isApp :: Term f -> Bool
isApp App{} = True
isApp _     = False

-- | Check if a term is a variable
isVar :: Term f -> Bool
isVar Var{} = True
isVar _     = False

-- | @t \`'isInstanceOf'\` pat@ checks if @t@ is an instance of @pat@.
isInstanceOf :: Term f -> Term f -> Bool
t `isInstanceOf` pat = isJust (match pat t)

-- | Check if two terms are renamings of one another.
isVariantOf :: Term f -> Term f -> Bool
t `isVariantOf` u = t `isInstanceOf` u && u `isInstanceOf` t

-- | Is a term a subterm of another one?
isSubtermOf :: Term f -> Term f -> Bool
t `isSubtermOf` u = t `isSubtermOfList` singleton u

-- | Map a function over the function symbols in a term.
mapFun :: (Fun f -> Fun g) -> Term f -> Builder g
mapFun f = mapFunList f . singleton

-- | Map a function over the function symbols in a termlist.
mapFunList :: (Fun f -> Fun g) -> TermList f -> Builder g
mapFunList f ts = aux ts
  where
    aux Empty = mempty
    aux (Cons (Var x) ts) = var x `mappend` aux ts
    aux (Cons (App ff ts) us) = app (f ff) (aux ts) `mappend` aux us

-- | Replace the term at a given position in a term with a different term.
{-# INLINE replacePosition #-}
replacePosition :: (Build a, BuildFun a ~ f) => Int -> a -> TermList f -> Builder f
replacePosition n !x = aux n
  where
    aux !_ !_ | False = undefined
    aux _ Empty = mempty
    aux 0 (Cons _ t) = builder x `mappend` builder t
    aux n (Cons (Var x) t) = var x `mappend` aux (n-1) t
    aux n (Cons t@(App f ts) u)
      | n < len t =
        app f (aux (n-1) ts) `mappend` builder u
      | otherwise =
        builder t `mappend` aux (n-len t) u

-- | Replace the term at a given position in a term with a different term, while
-- simultaneously applying a substitution. Useful for building critical pairs.
{-# INLINE replacePositionSub #-}
replacePositionSub :: (Substitution sub, SubstFun sub ~ f) => sub -> Int -> TermList f -> TermList f -> Builder f
replacePositionSub sub n !x = aux n
  where
    aux !_ !_ | False = undefined
    aux _ Empty = mempty
    aux n (Cons t u)
      | n < len t = inside n t `mappend` outside u
      | otherwise = outside (singleton t) `mappend` aux (n-len t) u

    inside 0 _ = outside x
    inside n (App f ts) = app f (aux (n-1) ts)
    inside _ _ = undefined -- implies n >= len t

    outside t = substList sub t

-- | Convert a position in a term, expressed as a single number, into a path.
positionToPath :: Term f -> Int -> [Int]
positionToPath t n = term t n
  where
    term _ 0 = []
    term t n = list 0 (children t) (n-1)

    list _ Empty _ = error "bad position"
    list k (Cons t u) n
      | n < len t = k:term t n
      | otherwise = list (k+1) u (n-len t)

-- | Convert a path in a term into a position.
pathToPosition :: Term f -> [Int] -> Int
pathToPosition t ns = term 0 t ns
  where
    term k _ [] = k
    term k t (n:ns) = list (k+1) (children t) n ns

    list _ Empty _ _ = error "bad path"
    list k (Cons t _) 0 ns = term k t ns
    list k (Cons t u) n ns =
      list (k+len t) u (n-1) ns

-- | A pattern which extracts the 'fun_value' from a 'Fun'.
pattern F :: f -> Fun f
pattern F x <- (fun_value -> x)

-- | Compare the 'fun_value's of two 'Fun's.
(<<) :: Ord f => Fun f -> Fun f -> Bool
f << g = fun_value f < fun_value g
