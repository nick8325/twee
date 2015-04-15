module KBC.Pretty where

import Text.PrettyPrint.HughesPJClass
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Ratio

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

supply :: [String] -> [String]
supply names =
  names ++
  [ name ++ show i | i <- [2..], name <- names ]
