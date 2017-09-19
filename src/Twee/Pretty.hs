-- | Pretty-printing of terms and assorted other values.

{-# LANGUAGE Rank2Types #-}
module Twee.Pretty(module Twee.Pretty, module Text.PrettyPrint.HughesPJClass, Pretty(..)) where

import Text.PrettyPrint.HughesPJClass hiding (empty)
import qualified Text.PrettyPrint.HughesPJClass as PP
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Ratio
import Twee.Term

-- * Miscellaneous 'Pretty' instances and utilities.

-- | Print a value to the console.
prettyPrint :: Pretty a => a -> IO ()
prettyPrint x = putStrLn (prettyShow x)

-- | The empty document. Used to avoid name clashes with 'Twee.Term.empty'.
pPrintEmpty :: Doc
pPrintEmpty = PP.empty

instance Pretty Doc where pPrint = id

-- | Print a tuple of values.
pPrintTuple :: [Doc] -> Doc
pPrintTuple = parens . fsep . punctuate comma

instance Pretty a => Pretty (Set a) where
  pPrint = pPrintSet . map pPrint . Set.toList

-- | Print a set of vlaues.
pPrintSet :: [Doc] -> Doc
pPrintSet = braces . fsep . punctuate comma

instance Pretty Var where
  pPrint (V n) =
    text $
      vars !! (n `mod` length vars):
      case n `div` length vars of
        0 -> ""
        m -> show (m+1)
    where
      vars = "XYZWVUTS"

instance (Pretty k, Pretty v) => Pretty (Map k v) where
  pPrint = pPrintSet . map binding . Map.toList
    where
      binding (x, v) = hang (pPrint x <+> text "=>") 2 (pPrint v)

instance (Eq a, Integral a, Pretty a) => Pretty (Ratio a) where
  pPrint a
    | denominator a == 1 = pPrint (numerator a)
    | otherwise = text "(" <+> pPrint (numerator a) <> text "/" <> pPrint (denominator a) <+> text ")"

-- | Generate a list of candidate names for pretty-printing.
supply :: [String] -> [String]
supply names =
  names ++
  [ name ++ show i | i <- [2..], name <- names ]

-- * Pretty-printing of terms.

instance Pretty f => Pretty (Fun f) where
  pPrintPrec l p = pPrintPrec l p . fun_value

instance PrettyTerm f => PrettyTerm (Fun f) where
  termStyle f = termStyle (fun_value f)

instance PrettyTerm f => Pretty (Term f) where
  pPrintPrec l p (Var x) = pPrintPrec l p x
  pPrintPrec l p (App f xs) =
    pPrintTerm (termStyle f) l p (pPrint f) (unpack xs)

instance PrettyTerm f => Pretty (TermList f) where
  pPrintPrec _ _ = pPrint . unpack

instance PrettyTerm f => Pretty (Subst f) where
  pPrint sub = text "{" <> fsep (punctuate (text ",") docs) <> text "}"
    where
      docs =
        [ hang (pPrint x <+> text "->") 2 (pPrint t)
        | (x, t) <- substToList sub ]

-- | A class for customising the printing of function symbols.
class Pretty f => PrettyTerm f where
  -- | The style of the function symbol. Defaults to 'curried'.
  termStyle :: f -> TermStyle
  termStyle _ = curried

-- | Defines how to print out a function symbol.
newtype TermStyle =
  TermStyle {
    -- | Renders a function application.
    -- Takes the following arguments in this order:
    -- Pretty-printing level, current precedence,
    -- pretty-printed function symbol and list of arguments to the function.
    pPrintTerm :: forall a. Pretty a => PrettyLevel -> Rational -> Doc -> [a] -> Doc }

invisible, curried, uncurried, prefix, postfix :: TermStyle

-- | For operators like @$@ that should be printed as a blank space.
invisible =
  TermStyle $ \l p d ->
    let
      f [] = d
      f [t] = pPrintPrec l p t
      f (t:ts) =
        maybeParens (p > 10) $
          pPrint t <+>
            (hsep (map (pPrintPrec l 11) ts))
    in f

-- | For functions that should be printed curried.
curried =
  TermStyle $ \l p d ->
    let
      f [] = d
      f xs =
        maybeParens (p > 10) $
          d <+>
            (hsep (map (pPrintPrec l 11) xs))
    in f

-- | For functions that should be printed uncurried.
uncurried =
  TermStyle $ \l _ d ->
    let
      f [] = d
      f xs =
        d <> parens (hsep (punctuate comma (map (pPrintPrec l 0) xs)))
    in f

-- | A helper function that deals with under- and oversaturated applications.
fixedArity :: Int -> TermStyle -> TermStyle
fixedArity arity style =
  TermStyle $ \l p d ->
    let
      f xs
        | length xs < arity = pPrintTerm curried l p (parens d) xs
        | length xs > arity =
            maybeParens (p > 10) $
              hsep (pPrintTerm style l 11 d ys:
                    map (pPrintPrec l 11) zs)
        | otherwise = pPrintTerm style l p d xs
        where
          (ys, zs) = splitAt arity xs
    in f

-- | A helper function that drops a certain number of arguments.
implicitArguments :: Int -> TermStyle -> TermStyle
implicitArguments n (TermStyle pp) =
  TermStyle $ \l p d xs -> pp l p d (drop n xs)

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
infixStyle :: Int -> TermStyle
infixStyle pOp =
  fixedArity 2 $
  TermStyle $ \l p d [x, y] ->
    maybeParens (p > fromIntegral pOp) $
      pPrintPrec l (fromIntegral pOp+1) x <+> d <+>
      pPrintPrec l (fromIntegral pOp+1) y

-- | For tuples.
tupleStyle :: TermStyle
tupleStyle =
  TermStyle $ \l _ _ xs ->
    parens (hsep (punctuate comma (map (pPrintPrec l 0) xs)))
