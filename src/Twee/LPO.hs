{-# LANGUAGE CPP, PatternGuards #-}
module Twee.LPO where

#include "errors.h"
import Twee.Base hiding (lessEq, lessIn)
import Twee.Constraints
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.List
import Debug.Trace
import Control.Monad

lessEq :: Function f => Term f -> Term f -> Bool
lessEq t u = isJust (lessIn (Model Map.empty) t u)

lessIn :: Function f => Model f -> Term f -> Term f -> Maybe Strictness
--lessIn model t u | traceShow (text "Checking" <+> pPrint t <+> text "<" <+> pPrint u <+> text "in" <+> pPrint model) False = undefined
lessIn model u@(Var x) t
  | or [isJust (varLessIn x u) | u <- properSubterms t] = traceRes u t $ Just Strict
  | Just str <- varLessIn x t = traceRes u t $ Just str
  | otherwise = traceRes u t Nothing
  where
    varLessIn x t = fromTerm t >>= lessEqInModel model (Variable x)
lessIn model t u@(Var x) = traceRes t u $ do
  a <- fromTerm t
  lessEqInModel model a (Variable x)
lessIn model t@(Fun f ts) u@(Fun g us) =
  traceRes t u $ 
  case compare f g of
    LT -> do
      guard (and [ lessIn model t u == Just Strict | t <- fromTermList ts ])
      return Strict
    EQ -> lexLess t u ts us
    GT -> do
      msum [ lessIn model t u | u <- fromTermList us ]
      return Strict
  where
    lexLess _ _ Empty Empty = Just Nonstrict
    lexLess t u (Cons t' ts) (Cons u' us)
      | t' == u' = lexLess t u ts us
      | Just str <- lessIn model t' u' = do
        guard (and [ lessIn model t u == Just Strict | t <- fromTermList ts ])
        case str of
          Strict -> Just Strict
          Nonstrict ->
            let Just sub = unify t' u' in
            lexLess (subst sub t) (subst sub u) (subst sub ts) (subst sub us)
      | otherwise = do
        msum [ lessIn model t u | u <- fromTermList us ]
        return Strict
    lexLess _ _ _ _ = ERROR("incorrect function arity")

-- traceRes t u res =
--   traceShow (pPrint t <+> text "<" <+> pPrint u <> text ":" <+> text (show res)) res
traceRes _ _ x = x
