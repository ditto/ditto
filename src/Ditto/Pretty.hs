module Ditto.Pretty where

import Ditto.Syntax
import Text.PrettyPrint.Boxes

----------------------------------------------------------------------

ppExp :: Exp -> Box
ppExp = ppwExp NoWrap

ppBind :: Name -> Exp -> Box
ppBind x _A = parens $ ppName x <+> oft <+> ppExp _A

ppwExp :: Wrap -> Exp -> Box
ppwExp w Type = text "Type"
ppwExp w (Var x) = ppName x
ppwExp w (Pi _A (Bind x _B)) = righty w $ ppBind x _A <+> oft <+> ppExp _B
ppwExp w (Lam _A (Bind x a)) = righty w $ ppBind x _A <+> arr <+> ppExp a
ppwExp w (Form _X _Is) = ppPrim w _X _Is
ppwExp w (Con x as) = ppPrim w x as
ppwExp w (Red x as) = ppPrim w x as
ppwExp w (f :@: a) = lefty w $ ppwExp NoWrapL f <+> ppwExp Wrap a

ppPrim :: Wrap -> PName -> [Exp] -> Box
ppPrim w x [] = ppPName x
ppPrim w x as = lefty w $ ppPName x <+> hsep 1 top (map (ppwExp Wrap) as)

----------------------------------------------------------------------

data Wrap = Wrap | NoWrapL | NoWrap

righty :: Wrap -> Box -> Box
righty NoWrap = id
righty _ = parens

lefty :: Wrap -> Box -> Box
lefty NoWrap = id
lefty NoWrapL = id
lefty Wrap = parens

----------------------------------------------------------------------

ppSig :: Sigma -> Box
ppSig (Def x a _A) = (ppName x <+> oft <+> ppExp _A) // (ppName x <+> def <+> ppExp a)
ppSig (DForm _X _Is) = ppPName _X <+> text "Data"
ppSig (DCon _Y _As _X _Is) = ppPName _Y <+> text "constructor of" <+> ppPName _X
ppSig (DRed x cs _As _B) = ppPName x <+> text "Reduction"

----------------------------------------------------------------------

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
def = text "="

----------------------------------------------------------------------