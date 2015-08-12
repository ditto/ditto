module Ditto.Pretty where

import Ditto.Syntax
import Text.PrettyPrint.Boxes

ppSig :: Sigma -> Box
ppSig (Def x a _A) = ppName x <+> oft <+> ppExp _A <+> eq <+> ppExp a
ppSig (Virt x a _A) = ppName x <+> oft <+> ppExp _A <+> eqv <+> ppExp a
ppSig (DForm _X _Is) = ppPName _X <+> text "Data"
ppSig (DCon _Y _As _X _Is) = ppPName _Y <+> text "constructor of" <+> ppPName _X

ppExp :: Exp -> Box
ppExp Type = text "Type"
ppExp (Pi x _A _B) = parens (ppName x <+> oft <+> ppExp _A) <+> oft <+> ppExp _B
ppExp (Lam x _A a) = parens (ppName x <+> oft <+> ppExp _A) <+> arr <+> ppExp a
ppExp (Form _X _Is) = ppPName _X
ppExp (Con _X as) = ppPName _X
ppExp (Elim _X _) = parens $ text "elim" <+> ppPName _X <+> text "..."
ppExp (Var x) = ppName x
ppExp (f :@: a) = (parens $ ppExp f) <+> (parens $ ppExp a)

ppName :: Name -> Box
ppName = text

ppPName :: PName -> Box
ppPName = text . ("#"++) . fromPName

----------------------------------------------------------------------

parens :: Box -> Box
parens d = char '(' <> d <> char ')'

oft :: Box
oft = char ':'

arr :: Box
arr = text "->"

eq :: Box
eq = text ":="

eqv :: Box
eqv = text ":=v"
