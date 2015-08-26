{-# LANGUAGE TypeFamilies, StandaloneDeriving, FlexibleContexts, UndecidableInstances, PartialTypeSignatures, RecordWildCards #-}
module KBC.Rewrite where

import KBC.Base
import KBC.Constraints
import qualified KBC.Index as Index
import KBC.Index(Index)
import KBC.Term
import Control.Monad
import Data.Maybe

data Rule f =
  Rule {
    orientation :: Orientation f,
    lhs :: Tm f,
    rhs :: Tm f }
  deriving (Eq, Ord, Show)

data Orientation f = Oriented | WeaklyOriented [Tm f] | Unoriented deriving (Eq, Ord, Show)

instance Symbolic (Rule f) where
  type ConstantOf (Rule f) = f
  termsDL Rule{..} = termsDL lhs `mplus` termsDL rhs
  substf sub (Rule or l r) = Rule (substf sub or) (substf sub l) (substf sub r)

instance Symbolic (Orientation f) where
  type ConstantOf (Orientation f) = f
  termsDL Oriented = mzero
  termsDL (WeaklyOriented ts) = msum (map termsDL ts)
  termsDL Unoriented = mzero
  substf sub Oriented = Oriented
  substf sub (WeaklyOriented ts) = WeaklyOriented (map (substf sub) ts)
  substf sub Unoriented = Unoriented

instance PrettyTerm f => Pretty (Rule f) where
  pPrint (Rule Oriented l r) = pPrintRule l r
  pPrint (Rule (WeaklyOriented ts) l r) = pPrintRule l r <+> text "(weak on" <+> pPrint ts <> text ")"
  pPrint (Rule Unoriented l r) = pPrintRule l r <+> text "(unoriented)"

pPrintRule :: PrettyTerm f => Tm f -> Tm f -> Doc
pPrintRule l r = hang (pPrint l <+> text "->") 2 (pPrint r)

type Strategy f = Tm f -> [Reduction f]

data Reduction f =
  Reduction {
    result :: Tm f,
    proof  :: Proof f }
  deriving Show

data Proof f =
    Refl
  | Step (Rule f)
  | Trans (Proof f) (Proof f)
  | Parallel f [Proof f]
  deriving Show

steps :: Reduction f -> [Rule f]
steps r = aux (proof r) []
  where
    aux Refl = id
    aux (Step r) = (r:)
    aux (Trans p q) = aux p . aux q
    aux (Parallel _ ps) = foldr (.) id (map aux ps)

refl :: Tm f -> Reduction f
refl t = Reduction t Refl

step :: Rule f -> Reduction f
step r = Reduction (rhs r) (Step r)

trans :: Reduction f -> Reduction f -> Reduction f
trans ~(Reduction _ p) (Reduction t q) = Reduction t (p `Trans` q)

parallel :: f -> [Reduction f] -> Reduction f
parallel f rs =
  Reduction
    (Fun f (map result rs))
    (Parallel f (map proof rs))

normaliseWith :: PrettyTerm f => Strategy f -> Tm f -> Reduction f
normaliseWith strat t =
  case strat t of
    p:_ -> continue p
    [] ->
      case t of
        Fun f ts | not (all (null . steps) ns) ->
          continue (parallel f ns)
          where
            ns = map (normaliseWith strat) ts
        _ -> refl t
  where
    continue p = p `trans` normaliseWith strat (result p)

anywhere :: Strategy f -> Strategy f
anywhere strat t = strat t ++ nested (anywhere strat) t

nested _ Var{} = []
nested strat (Fun f xs) =
  [ parallel f $
      map refl (take (i-1) xs) ++ [p] ++ map refl (drop i xs)
  | (i, x) <- zip [0..] xs,
    p <- strat x ]

allowedInModel :: (Ord f, Sized f, Minimal f, PrettyTerm f) =>
  [Formula f] -> Rule f -> Bool
allowedInModel _ (Rule Oriented _ _) = True
allowedInModel _ (Rule (WeaklyOriented xs) _ _) =
  or [x /= minimalTerm | x <- xs]
allowedInModel cond (Rule Unoriented t u) =
  lessEqIn cond u t && t /= u

allowedSkolem :: (Ord f, Sized f, Minimal f, PrettyTerm f) =>
  Rule f -> Bool
allowedSkolem (Rule Oriented _ _) = True
allowedSkolem (Rule (WeaklyOriented xs) _ _) =
  or [x /= minimalTerm | x <- xs]
allowedSkolem (Rule Unoriented t u) =
  lessEq (skolemise u) (skolemise t) && t /= u

allowedSub :: (Ord f, Numbered f, Sized f, Minimal f, PrettyTerm f) =>
  Tm f -> Rule f -> Bool
allowedSub top rule =
  allowedSkolem rule && lessEq u top && isNothing (unify u top)
  where
    u = rhs rule

rewriteInModel :: (Ord f, Numbered f, Sized f, Minimal f, PrettyTerm f) =>
  Index (Rule f) -> [Formula f] -> Strategy f
rewriteInModel rules model t = do
  rule <- Index.lookup t rules
  guard (allowedInModel model rule)
  return (step rule)

rewriteSub :: (Ord f, Numbered f, Sized f, Minimal f, PrettyTerm f) =>
  Index (Rule f) -> Tm f -> Strategy f
rewriteSub rules top t = do
  rule <- Index.lookup t rules
  guard (allowedSub top rule)
  return (step rule)

simplify :: (PrettyTerm f, Numbered f, Sized f, Minimal f, Ord f) => Index (Rule f) -> Strategy f
simplify rules t = do
  rule <- Index.lookup t rules
  case orientation rule of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ t /= minimalTerm | t <- ts ])
    Unoriented -> mzero
  return (step rule)

rewrite :: (PrettyTerm f, Numbered f, Sized f, Minimal f, Ord f) => Index (Rule f) -> Strategy f
rewrite rules t = do
  rule <- Index.lookup t rules
  case orientation rule of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ t /= minimalTerm | t <- ts ])
    Unoriented -> guard (lessEq (rhs rule) (lhs rule) && rhs rule /= lhs rule)
  return (step rule)

tryRule :: (Ord f, Sized f, Minimal f) => Rule f -> Strategy f
tryRule rule t = do
  sub <- maybeToList (match (lhs rule) t)
  let rule' = substf (evalSubst sub) rule
  case orientation rule' of
    Oriented -> return ()
    WeaklyOriented ts -> guard (or [ t /= minimalTerm | t <- ts ])
    Unoriented -> guard (lessEq (rhs rule') (lhs rule') && rhs rule' /= lhs rule')
  return (step rule')

tryRuleInModel :: (Ord f, Sized f, Minimal f, PrettyTerm f) => [Formula f] -> Rule f -> Strategy f
tryRuleInModel model rule t = do
  sub <- maybeToList (match (lhs rule) t)
  let rule' = substf (evalSubst sub) rule
  guard (allowedInModel model rule')
  return (step rule')
