-- | Pretty-printing of terms and assorted other values.

{-# LANGUAGE CPP, Rank2Types #-}
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

-- * Miscellaneous 'Pretty' instances and utilities.

prettyPrint :: Pretty a => a -> IO ()
prettyPrint x = putStrLn (prettyShow x)

pPrintParen :: Bool -> Doc -> Doc
pPrintParen True  d = parens d
pPrintParen False d = d

instance Pretty Doc where pPrint = id

pPrintTuple :: [Doc] -> Doc
pPrintTuple = parens . fsep . punctuate comma

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

instance (PrettyTerm f, Pretty v) => Pretty (Rule f v) where
  pPrint (Rule l r) =
    hang (pPrint l <+> text "->") 2 (pPrint r)

-- | Generate a list of candidate names for pretty-printing.
supply :: [String] -> [String]
supply names =
  names ++
  [ name ++ show i | i <- [2..], name <- names ]

-- * Pretty-printing of terms.

instance (PrettyTerm f, Pretty v) => Pretty (Term f v) where
  pPrintPrec l p (Var x) = pPrintPrec l p x
  pPrintPrec l p (Fun f xs) = pPrintTerm (termStyle f) l p (pPrint f) xs

-- | A class for customising the printing of function symbols.
class Pretty a => PrettyTerm a where
  termStyle :: a -> TermStyle
  termStyle _ = curried

-- | Defines how to print out a function symbol.
newtype TermStyle =
  TermStyle {
    -- | Takes the pretty-printing level, precedence,
    -- pretty-printed function symbol and list of arguments and prints the term.
    pPrintTerm :: forall a. Pretty a => PrettyLevel -> Rational -> Doc -> [a] -> Doc }

invisible, curried, uncurried, prefix, postfix :: TermStyle

-- | For operators like @$@ that should be printed as a blank space.
invisible =
  TermStyle $ \l p d ->
    let
      f [] = d
      f [t] = pPrintPrec l p t
      f (t:ts) =
        pPrintParen (p > 10) $
          hang (pPrint t) 2
            (fsep (map (pPrintPrec l 11) ts))
    in f

-- | For functions that should be printed curried.
curried =
  TermStyle $ \l p d ->
    let
      f [] = d
      f xs =
        pPrintParen (p > 10) $
          hang d 2
            (fsep (map (pPrintPrec l 11) xs))
    in f

-- | For functions that should be printed uncurried.
uncurried =
  TermStyle $ \l _ d ->
    let
      f [] = d
      f xs =
        d <> parens (fsep (punctuate comma (map (pPrintPrec l 0) xs)))
    in f

-- | A helper function that deals with under- and oversaturated applications.
fixedArity :: Int -> TermStyle -> TermStyle
fixedArity arity style =
  TermStyle $ \l p d ->
    let
      f xs
        | length xs < arity = pPrintTerm curried l p (parens d) xs
        | length xs > arity =
            pPrintParen (p > 10) $
              fsep (parens (pPrintTerm style l 0 d ys):
                    map (nest 2 . pPrintPrec l 11) zs)
        | otherwise = pPrintTerm style l p d xs
        where
          (ys, zs) = splitAt arity xs
    in f

-- | For prefix operators.
prefix =
  fixedArity 1 $
  TermStyle $ \l _ d [x] ->
    d <> pPrintPrec l 11 x

-- | For postfix operators.
postfix =
  fixedArity 1 $
  TermStyle $ \l _ d [x] ->
    pPrintPrec l 11 x <> d

-- | For infix operators.
-- e.g. @infixStyle (Left 5)@ corresponds to @infixl 5@.
-- Currently terms that mix left- and right-associative
-- operators are not printed correctly.
infixStyle :: Either Int Int -> TermStyle
infixStyle fixity =
  fixedArity 2 $
  TermStyle $ \l p d [x, y] ->
    pPrintParen (p > pOp) $
      hang (pPrintPrec l (pOp+1) x <+> d) 2
           (pPrintPrec l (pOp+r) y)
  where
    (r, pOp) =
      case fixity of
        Left pOp -> (0, fromIntegral pOp)
        Right pOp -> (1, fromIntegral pOp)
