{-# LANGUAGE ViewPatterns #-}
module Ditto.Pretty where

import Ditto.Syntax
import Ditto.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Text.PrettyPrint.Boxes

----------------------------------------------------------------------

throwNotInScope :: Name -> TCM a
throwNotInScope x = do
  DittoR {ctx = ctx} <- ask
  DittoS {sig = sig} <- get
  throwError $ renderNotInScope x ++ renderCtx ctx ++ renderEnv sig

throwNotConv :: Exp -> Exp -> TCM a
throwNotConv a b = do
  DittoR {ctx = ctx} <- ask
  DittoS {sig = sig} <- get
  throwError $
       renderNotConv a b
    ++ renderCtx ctx
    ++ renderEnv sig

----------------------------------------------------------------------

renderCtx :: Tel -> String
renderCtx ctx = "\nContext:\n\n" ++ concat (map (render . ppCtxBind) (reverse ctx))

renderEnv :: [Sigma] -> String
renderEnv sig = "\nEnvironment:\n\n" ++ unlines (map (render . ppSig) (reverse sig))

renderNotInScope :: Name -> String
renderNotInScope x = render $ text "Variable not in scope:" <+> ppName x

renderNotConv :: Exp -> Exp -> String
renderNotConv x y = render $ text "Terms not convertible:" <+> ppExp x <+> text "!=" <+> ppExp y

----------------------------------------------------------------------

ppExp :: Exp -> Box
ppExp = ppwExp NoWrap

ppwExp :: Wrap -> Exp -> Box
ppwExp w Type = text "Type"
ppwExp w (Var x) = ppName x
ppwExp w x@(Pi _ _) = ppPis w x
ppwExp w x@(Lam _ _) = ppLams w x
ppwExp w (Form _X _Is) = ppPrim w _X _Is
ppwExp w (Con x as) = ppPrim w x as
ppwExp w (Red x as) = ppPrim w x as
ppwExp w (f :@: a) = lefty w $ ppwExp NoWrapL f <+> ppwExp Wrap a

ppPrim :: Wrap -> PName -> [Exp] -> Box
ppPrim w x [] = ppPName x
ppPrim w x as = lefty w $ ppPName x <+> hcatmap (ppwExp Wrap) as

----------------------------------------------------------------------

ppPis :: Wrap -> Exp -> Box
ppPis w (viewPis -> (_As, _B)) = righty w $ hcatmap (uncurry ppBind) _As <+> oft <+> ppExp _B

ppLams :: Wrap -> Exp -> Box
ppLams w (viewLams -> (as, b)) = righty w $ hcatmap (uncurry ppBind) as <+> arr <+> ppExp b

viewPis :: Exp -> ([(Name, Exp)], Exp)
viewPis (Pi _A (Bind x _B)) = ((x, _A):_As, _B')
  where (_As, _B') = viewPis _B
viewPis a = ([], a)

viewLams :: Exp -> ([(Name, Exp)], Exp)
viewLams (Lam _A (Bind x b)) = ((x, _A):_As, b')
  where (_As, b') = viewLams b
viewLams a = ([], a)

ppBind :: Name -> Exp -> Box
ppBind x _A = parens $ curry ppCtxBind x _A

ppCtxBind :: (Name, Exp) -> Box
ppCtxBind (x, _A) = ppName x <+> oft <+> ppExp _A

----------------------------------------------------------------------

ppPat :: Pat -> Box
ppPat (PVar x) = ppName x
ppPat (Inacc Nothing) = text "*"
ppPat (Inacc (Just a)) = text "." <> ppwExp Wrap a
ppPat (PCon x []) = ppPName x
ppPat (PCon x ps) = parens $ ppPName x <+> hcatmap ppPat ps

----------------------------------------------------------------------

data Wrap = Wrap | NoWrapL | NoWrap

righty :: Wrap -> Box -> Box
righty NoWrap = id
righty _ = parens

lefty :: Wrap -> Box -> Box
lefty Wrap = parens
lefty _ = id

----------------------------------------------------------------------

ppSig :: Sigma -> Box
ppSig (Def x a _A) = ppDefType x _A // ppDefBod x a
ppSig (DForm _X _Is) = brackets $ ppPName _X <+> text "type former"
ppSig (DCon _Y _As _X _Is) = brackets $ ppPName _Y <+> text "constructor of" <+> ppPName _X
ppSig (DRed x cs _As _B) = brackets (ppPName x <+> text "reduction rules")
  /+/ vcatmap (ppRed x) cs

----------------------------------------------------------------------

ppRed :: PName -> CheckedClause -> Box
ppRed x (_As, ps, rhs) = ppRedCtx x _As //
  (ppPName x <+> hcatmap ppPat ps <+> def <+> ppExp rhs)

ppRedCtx :: PName -> Tel -> Box
ppRedCtx x [] = ppPName x <+> text "[empty context]"
ppRedCtx x [_A] = ppPName x <+> oft <+> uncurry ppBind _A
ppRedCtx x _As = ppPName x <+> hcatmap (uncurry ppBind) _As

----------------------------------------------------------------------

ppDefType :: Name -> Exp -> Box
ppDefType x _A@(Pi _ _) = ppName x <+> ppExp _A
ppDefType x _A = ppName x <+> oft <+> ppExp _A

ppDefBod :: Name -> Exp -> Box
ppDefBod x a@(Lam _ _) = ppName x <+> ppExp a
ppDefBod x a = ppName x <+> def <+> ppExp a

----------------------------------------------------------------------

ppName :: Name -> Box
ppName = text . show

ppPName :: PName -> Box
ppPName = text . show

----------------------------------------------------------------------

parens :: Box -> Box
parens d = char '(' <> d <> char ')'

brackets :: Box -> Box
brackets d = char '[' <> d <> char ']'

oft :: Box
oft = char ':'

arr :: Box
arr = text "="

def :: Box
def = text "="

vcatmap :: (a -> Box) -> [a] -> Box
vcatmap f xs = vsep 1 left (map f xs)

hcatmap :: (a -> Box) -> [a] -> Box
hcatmap f xs = hsep 1 top (map f xs)

----------------------------------------------------------------------