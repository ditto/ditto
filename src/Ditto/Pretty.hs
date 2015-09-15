module Ditto.Pretty where

import Ditto.Syntax
import Ditto.Monad
import Ditto.Env
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Applicative
import Text.PrettyPrint.Boxes

----------------------------------------------------------------------

throwNotInScope :: Name -> TCM a
throwNotInScope x = do
  ctx <- renderCtxEnv
  throwError $ renderNotInScope x ++ ctx

throwNotConv :: Exp -> Exp -> TCM a
throwNotConv a b = do
  ctx <- renderCtxEnv
  acts <- getActs
  throwError $ renderNotConv a b ctx acts

throwUnsolvedMetas :: [(MName, Tel, Exp)] -> TCM a
throwUnsolvedMetas = throwError . renderUnsolvedMetas

renderCtxEnv :: TCM String
renderCtxEnv = do
  ctx <- getCtx
  env <- getEnv
  getVerbosity >>= \case
    Normal -> return $ renderCtx ctx
    Verbose -> return $ renderCtx ctx ++ renderEnv env

----------------------------------------------------------------------

renderCtx :: Ctx -> String
renderCtx ctx = "\nContext:\n\n" ++ concat (map (render . ppCtxBind) (reverse ctx))

renderEnv :: Env -> String
renderEnv env = "\nEnvironment:\n\n" ++ unlines (map (render . ppSig) (reverse env))

renderNotInScope :: Name -> String
renderNotInScope x = render $ text "Variable not in scope:" <+> ppName x

renderNotConv :: Exp -> Exp -> String -> Acts -> String
renderNotConv x y ctx acts = render $
  text "Terms not convertible" <+> brackets (ppExp x <+> text "!=" <+> ppExp y)
  // ppActs acts
  // text ctx

renderUnsolvedMetas :: [(MName, Tel, Exp)] -> String
renderUnsolvedMetas xs = render $ text "Unsolved metavariables:" //
  vcatmap (\(x, _As, _B) -> ppMetaType x _As _B) xs

----------------------------------------------------------------------

ppActs :: Acts -> Box
ppActs xs = vcatmap0 ppAct xs

ppAct :: Act -> Box
ppAct (ACheck a _A) = while "checking" (ppExp a <+> oft <+> ppExp _A)
ppAct (AConv x y) = while "unifying" (ppExp x <+> eqs <+> ppExp y)

while :: String -> Box -> Box
while str x = text "...while" <+> text str <+> brackets x

----------------------------------------------------------------------

renderHoles :: Holes -> String
renderHoles [] = ""
renderHoles xs = render $ text "Holes:" // vcatmap ppHole xs

ppHole :: Hole -> Box
ppHole (x, a, (fromTel -> _As), _B) = (ppMName x <+> oft <+> ppExp _B)
  // line // vcatmap0 ppCtxBind _As

----------------------------------------------------------------------

ppExp :: Exp -> Box
ppExp = ppwExp NoWrap

ppArg :: (Icit, Exp) -> Box
ppArg (Expl, a) = ppwExp Wrap a
ppArg (Impl, a) = braces (ppExp a)

ppwExp :: Wrap -> Exp -> Box
ppwExp w Type = text "Type"
ppwExp w (Infer m) = ppInfer m
ppwExp w (Var x) = ppName x
ppwExp w x@(Pi _ _ _) = ppPis w x
ppwExp w x@(Lam _ _ _) = ppLams w x
ppwExp w (Form _X _Is) = ppPrim w _X _Is
ppwExp w (Con x as) = ppPrim w x as
ppwExp w (Red x as) = ppPrim w x as
ppwExp w (Meta x as) = ppMeta w x as
ppwExp w (App i f a) = lefty w $ ppwExp NoWrapL f <+> ppArg (i, a)

ppInfer :: MKind -> Box
ppInfer MInfer = forced
ppInfer MHole = hole

ppPrim :: Wrap -> PName -> Args -> Box
ppPrim w x [] = ppPName x
ppPrim w x as = lefty w $ ppPName x <+> hcatmap ppArg as

ppMeta :: Wrap -> MName -> Args -> Box
ppMeta w x [] = ppMName x
ppMeta w x as = lefty w $ ppMName x <+> hcatmap ppArg as

----------------------------------------------------------------------

ppPis :: Wrap -> Exp -> Box
ppPis w (viewPis -> (_As, _B)) = righty w $ hcatmap ppBind _As <+> oft <+> ppExp _B

ppLams :: Wrap -> Exp -> Box
ppLams w (viewLams -> (as, b)) = righty w $ hcatmap ppBind as <+> arr <+> ppExp b

viewPis :: Exp -> (Tel, Exp)
viewPis (Pi i _A (Bind x _B)) = ((i, x, _A):_As, _B')
  where (_As, _B') = viewPis _B
viewPis a = ([], a)

viewLams :: Exp -> (Tel, Exp)
viewLams (Lam i _A (Bind x b)) = ((i, x, _A):_As, b')
  where (_As, b') = viewLams b
viewLams a = ([], a)

ppBind :: (Icit, Name, Exp) -> Box
ppBind (Expl, x, _A) = parens $ curry ppCtxBind x _A
ppBind (Impl, x, _A) = braces $ curry ppCtxBind x _A

ppCtxBind :: (Name, Exp) -> Box
ppCtxBind (x, _A) = ppName x <+> oft <+> ppExp _A

----------------------------------------------------------------------

ppPat :: (Icit, Pat) -> Box
ppPat (Expl, p) = braces (ppPat' p)
ppPat (Impl, p) = ppPat' p

ppPat' :: Pat -> Box
ppPat' (PVar x) = ppName x
ppPat' (Inacc Nothing) = forced
ppPat' (Inacc (Just a)) = text "." <> ppwExp Wrap a
ppPat' (PCon x []) = ppPName x
ppPat' (PCon x ps) = parens $ ppPName x <+> ppPats ps

ppPats :: Pats -> Box
ppPats = hcatmap ppPat

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
  /+/ vcatmap (ppRed x) (reverse cs)
ppSig (DMeta x _ b _As _B) = ppDMeta x b _As _B

----------------------------------------------------------------------

ppRed :: PName -> CheckedClause -> Box
ppRed x (_As, ps, rhs) = ppRedCtx x _As //
  (ppPName x <+> ppPats ps <+> ppRHS rhs)

ppRHS :: RHS -> Box
ppRHS (Prog a) = def <+> ppExp a
ppRHS (Caseless x) = ndef <+> ppName x

ppRedCtx :: PName -> Ctx -> Box
ppRedCtx x _As = ppPName x <+> hcatmap (parens . ppCtxBind) _As

--------------------------------------------------------------------------------

ppDMeta :: MName -> Maybe Exp -> Tel -> Exp -> Box
ppDMeta x b _As _B = case b of
  Nothing -> ppMetaType x _As _B
  Just b -> ppMetaType x _As _B // ppMetaBod x b

ppMetaType :: MName -> Tel -> Exp -> Box
ppMetaType x _As@(_:_) _B = ppMName x <+> ppExp (metaType _As _B)
ppMetaType x [] _B = ppMName x <+> oft <+> ppExp _B

ppMetaBod :: MName -> Exp -> Box
ppMetaBod x a = ppMName x <+> def <+> ppExp a

----------------------------------------------------------------------

ppDefType :: Name -> Exp -> Box
ppDefType x _A@(Pi _ _ _) = ppName x <+> ppExp _A
ppDefType x _A = ppName x <+> oft <+> ppExp _A

ppDefBod :: Name -> Exp -> Box
ppDefBod x a = ppName x <+> def <+> ppExp a

----------------------------------------------------------------------

ppName :: Name -> Box
ppName = text . show

ppPName :: PName -> Box
ppPName = text . show

ppMName :: MName -> Box
ppMName = text . show

----------------------------------------------------------------------

parens :: Box -> Box
parens d = char '(' <> d <> char ')'

braces :: Box -> Box
braces d = char '{' <> d <> char '}'

brackets :: Box -> Box
brackets d = char '[' <> d <> char ']'

oft :: Box
oft = char ':'

arr :: Box
arr = text "->"

def :: Box
def = char '='

eqs :: Box
eqs = text "=="

ndef :: Box
ndef = text "!="

forced :: Box
forced = char '*'

hole :: Box
hole = char '?'

line :: Box
line = text (take 30 (repeat '-'))

vcatmap :: (a -> Box) -> [a] -> Box
vcatmap f xs = vsep 1 left (map f xs)

vcatmap0 :: (a -> Box) -> [a] -> Box
vcatmap0 f xs = vsep 0 left (map f xs)

hcatmap :: (a -> Box) -> [a] -> Box
hcatmap f xs = hsep 1 top (map f xs)

----------------------------------------------------------------------