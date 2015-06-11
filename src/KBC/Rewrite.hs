module KBC.Rewrite where

import KBC.Base
import KBC.Constraints
import qualified KBC.Index as Index
import KBC.Index(Index)
import KBC.Term
import Data.Rewriting.Rule
import Data.Map.Strict(Map)
import Data.Set(Set)
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe

type Strategy f v = Tm f v -> [Constrained (Rule f v)]

data Reduction f v =
  Reduction {
    result :: Tm f v,
    steps  :: [Constrained (Rule f v)] }
  deriving Show

normaliseWith :: Strategy f v -> Tm f v -> Reduction f v
normaliseWith strat t =
  aux [] t
  where
    aux rs t =
      case strat t of
        [] -> Reduction t (reverse rs)
        (r@(Constrained _ (Rule _ u)):_) -> aux (r:rs) u

anywhere :: Strategy f v -> Strategy f v
anywhere strat t = strat t ++ nested (anywhere strat) t

nested :: Strategy f v -> Strategy f v
nested _ Var{} = []
nested strat (Fun f xs) =
  [ Constrained ctx (Rule (Fun f ts) (Fun f us))
  | (ctx, ts, us) <- inner xs ]
  where
    inner [] = []
    inner (x:xs) =
      [ (ctx, y:xs, z:xs)
      | Constrained ctx (Rule y z) <- strat x ] ++
      [ (ctx, x:ys, x:zs) | (ctx, ys, zs) <- inner xs ]

rewriteInModel :: (PrettyTerm f, Pretty v, Numbered f, Sized f, Minimal f, Ord f, Numbered v, Ord v) => Index (Constrained (Rule f v)) -> Map v (Extended f v) -> Strategy f v
rewriteInModel rules model t = do
  rule <- Index.lookup t rules
  guard (trueIn model . formula . constraint $ rule)
  return rule

rewrite :: (Numbered f, Sized f, Minimal f, Ord f, Numbered v, Ord v) => Index (Constrained (Rule f v)) -> Strategy f v
rewrite rules t = do
  rule <- Index.lookup t rules
  guard (formula (constraint rule) == true)
  return rule

rewriteAllowing :: (Numbered f, Sized f, Minimal f, Ord f, Numbered v, Ord v) => Index (Constrained (Rule f v)) -> Set (Formula Simple f v) -> Strategy f v
rewriteAllowing rules forms t = do
  rule <- Index.lookup t rules
  guard (formula (constraint rule) == true ||
         formula (constraint rule) `Set.member` forms)
  return rule

tryRule :: (Ord f, Sized f, Minimal f, Ord v) => Constrained (Rule f v) -> Strategy f v
tryRule rule t = do
  sub <- maybeToList (match (lhs (constrained rule)) t)
  let rule' = substf (evalSubst sub) rule
  guard (formula (constraint rule') == true)
  return rule'

tryRuleInModel :: (Ord f, Sized f, Minimal f, Ord v) => Map v (Extended f v) -> Constrained (Rule f v) -> Strategy f v
tryRuleInModel model rule t = do
  sub <- maybeToList (match (lhs (constrained rule)) t)
  let rule' = substf (evalSubst sub) rule
  guard (trueIn model (formula (constraint rule')))
  return rule'
