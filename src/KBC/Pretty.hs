{-# LANGUAGE CPP #-}
module KBC.Pretty where

#include "errors.h"
import Text.PrettyPrint.HughesPJClass
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Ratio
import Data.Rewriting.Rule(Rule(..))
import Data.Rewriting.Term(Term(..))

instance Pretty Doc where pPrint = id

pPrintTuple :: [Doc] -> Doc
pPrintTuple = parens . fsep . punctuate comma

pPrintParen :: Bool -> Doc -> Doc
pPrintParen True  d = parens d
pPrintParen False d = d

prettyPrint :: Pretty a => a -> IO ()
prettyPrint x = putStrLn (prettyShow x)

instance Pretty a => Pretty (Set a) where
  pPrint = pPrintSet . map pPrint . Set.toList

pPrintSet :: [Doc] -> Doc
pPrintSet = braces . fsep . punctuate comma

instance (Pretty k, Pretty v) => Pretty (Map k v) where
  pPrint = pPrintSet . map binding . Map.toList
    where
      binding (x, v) = hang (pPrint x <+> text "=>") 2 (pPrint v)

instance (Eq a, Integral a, Pretty a) => Pretty (Ratio a) where
  pPrint a
    | denominator a == 1 = pPrint (numerator a)
    | otherwise = text "(" <+> pPrint a <+> text ")"

class Pretty a => PrettyTerm a where
  termStyle :: a -> TermStyle
  termStyle _ = Curried

data TermStyle = Invisible | Curried | Uncurried | Tuple Int | TupleType | ListType | Infix Int | Infixr Int | Prefix | Postfix | Gyrator deriving Show

instance (PrettyTerm f, Pretty v) => Pretty (Term f v) where
  pPrintPrec l p (Var x) = pPrintPrec l p x
  pPrintPrec l p (Fun f xs) =
    pPrintStyle (termStyle f) l p (pPrint f) xs

instance (PrettyTerm f, Pretty v) => Pretty (Rule f v) where
  pPrint (Rule l r) =
    hang (pPrint l <+> text "->") 2 (pPrint r)

pPrintStyle :: Pretty a => TermStyle -> PrettyLevel -> Rational -> Doc -> [a] -> Doc
pPrintStyle Invisible _ _ d [] = d
pPrintStyle Invisible l p _ [t] = pPrintPrec l p t
pPrintStyle Invisible l p _ (t:ts) =
  pPrintParen (p > 10) $
    hang (pPrint t) 2
      (fsep (map (pPrintPrec l 11) ts))
pPrintStyle Curried _ _ d [] = d
pPrintStyle Curried l p d xs =
  pPrintParen (p > 10) $
    hang d 2
      (fsep (map (pPrintPrec l 11) xs))
pPrintStyle Uncurried _ _ d [] = d
pPrintStyle Uncurried l _ d xs =
  d <> parens (fsep (punctuate comma (map (pPrintPrec l 0) xs)))
pPrintStyle (Tuple arity) l p _ xs
  | length xs >= arity =
    pPrintStyle Curried l p
      (pPrintTuple (take arity (map (pPrintPrec l 0) xs)))
      (drop arity xs)
  | otherwise =
    pPrintStyle Curried l p
      (text ("(" ++ replicate (arity-1) ',' ++ ")")) xs
pPrintStyle Postfix l _ d [x] =
  pPrintPrec l 11 x <> d
pPrintStyle Postfix l p d xs =
  pPrintStyle Curried l p (parens d) xs
pPrintStyle Prefix l _ d [x] =
  d <> pPrintPrec l 11 x
pPrintStyle Prefix l p d xs =
  pPrintStyle Curried l p (parens d) xs
pPrintStyle TupleType l p d xs =
  pPrintStyle (Tuple (length xs)) l p d xs
pPrintStyle ListType l _ _ [x] =
  brackets (pPrintPrec l 0 x)
pPrintStyle ListType l p d xs =
  pPrintStyle Curried l p d xs
pPrintStyle Gyrator l _ d [x, y] =
  d <> brackets (sep (punctuate comma [pPrintPrec l 0 x, pPrintPrec l 0 y]))
pPrintStyle Gyrator l p d (x:y:zs) =
  pPrintStyle Curried l p (pPrintStyle Gyrator l p d [x, y]) zs
pPrintStyle Gyrator l p d xs = pPrintStyle Curried l p d xs
pPrintStyle style l p d xs =
  case xs of
    [x, y] ->
      pPrintParen (p > pOp) $
        hang (pPrintPrec l (pOp+1) x <+> d) 2
             (pPrintPrec l (pOp+r) y)
    (x:y:xs) ->
      pPrintParen (p > pOp) $
        hang (pPrintStyle style l 11 d [x, y]) 2
          (fsep (map (pPrintPrec l 11) xs))
    [x] ->
      parens (pPrintPrec l (pOp+1) x <+> d)
    _ ->
      pPrintParen (p > pOp) $
        hang (parens d) 2
          (fsep (map (pPrintPrec l 11) xs))
  where
    (r, pOp) =
      case style of
        Infixr pOp -> (0, fromIntegral pOp)
        Infix  pOp -> (1, fromIntegral pOp)
        _ -> ERROR("unknown style")

supply :: [String] -> [String]
supply names =
  names ++
  [ name ++ show i | i <- [2..], name <- names ]
