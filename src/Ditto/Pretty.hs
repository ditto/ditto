module Ditto.Pretty where

import Ditto.Syntax
import Text.PrettyPrint.Boxes

ppSig :: Sigma -> Box
ppSig (Def x a _A) = ppName x <+> oft <+> ppExp _A <+> def <+> ppExp a
ppSig (DForm _X _Is) = ppPName _X <+> text "Data"
ppSig (DCon _Y _As _X _Is) = ppPName _Y <+> text "constructor of" <+> ppPName _X
ppSig (DRed x cs _As _B) = ppPName x <+> text "Reduction"

ppExp :: Exp -> Box
ppExp Type = text "Type"
ppExp (Pi _A (Bind x _B)) = parens (ppName x <+> oft <+> ppExp _A) <+> oft <+> ppExp _B
ppExp (Lam _A (Bind x a)) = parens (ppName x <+> oft <+> ppExp _A) <+> arr <+> ppExp a
ppExp (Form _X _Is) = ppPName _X
ppExp (Con _X as) = ppPName _X
ppExp (Red _X as) = ppPName _X
ppExp (Var x) = ppName x
ppExp (f :@: a) = (parens $ ppExp f) <+> (parens $ ppExp a)

ppName :: Name -> Box
ppName = text . show

ppPName :: PName -> Box
ppPName = text . show

----------------------------------------------------------------------

parens :: Box -> Box
parens d = char '(' <> d <> char ')'

oft :: Box
oft = char ':'

arr :: Box
arr = text "->"

def :: Box
def = text ":="

