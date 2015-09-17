module Ditto.Pretty where
import Ditto.Syntax
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Applicative
import Data.Maybe
import Text.PrettyPrint.Boxes

----------------------------------------------------------------------

ppErr :: Err -> Box
ppErr (EGen err) = text err
ppErr (EConv a b) = text "Terms not convertible"
  <+> code (ppExp a <+> neq <+> ppExp b)
ppErr (EScope x) = text "Variable not in scope"
  <+> code (ppName x)
ppErr (ECaseless x) = text "Variable is not caseless"
  <+> code (ppName x)
ppErr (EMetas xs) = text "Unsolved metavariables" //
  vcatmap (\(x, _As, _B) -> ppMetaType x _As _B) xs
ppErr (ECover x qs) = text "Uncovered clause"
  <+> code (ppPName x <+> ppPats qs)
ppErr (EReach x xs) = text "Unreachable clauses" //
  vcatmap (ppRed' x) xs

withCtx :: Acts -> Ctx -> Maybe Env -> Box -> Box
withCtx acts ctx menv x = vcatmaybes
  [ Just x
  , ppActs acts
  , ppCtx ctx
  , ppEnvVerb menv
  ]

----------------------------------------------------------------------

ppCtx :: Ctx -> Maybe Box
ppCtx [] = Nothing
ppCtx xs = Just $ sec "Context" // vcatmap0 ppCtxBind (reverse xs)

ppEnvVerb :: Maybe Env -> Maybe Box
ppEnvVerb = (>>= ppEnv)

ppEnv :: Env -> Maybe Box
ppEnv [] = Nothing
ppEnv xs = Just $ sec "Environment" // vcatmap0 ppSig (reverse xs)

sec :: String -> Box
sec str = textc str // line

----------------------------------------------------------------------

ppActs :: Acts -> Maybe Box
ppActs [] = Nothing
ppActs xs = Just $ vcatmap0 ppAct xs

ppAct :: Act -> Box
ppAct (ADef x) = while "checking definition" $ ppName x
ppAct (ADefn x) = while "checking function" $ ppPName x
ppAct (AData x) = while "checking datatype" $ ppPName x
ppAct (ACon x) = while "checking constructor" $ ppPName x

ppAct (ACheck a _A) = while "checking" $ ppwExp Wrap a <+> oft <+> ppExp _A
ppAct (AInfer a) = while "inferring" $ ppExp a
ppAct (AConv x y) = while "equating" $ ppExp x <+> eq <+> ppExp y
ppAct (ACover x qs) = while "covering" $ ppPName x <+> ppPats qs

while :: String -> Box -> Box
while str x = text "...while" <+> text str <+> code x

----------------------------------------------------------------------

renderHoles :: Holes -> String
renderHoles [] = ""
renderHoles xs = render $ vcatmap ppHole xs

ppHole :: Hole -> Box
ppHole (x, a, (fromTel -> _As), _B) = (text "Hole" <+> ppMName x <+> oft <+> ppExp _B)
  // line // vcatmap0 ppCtxBind (reverse _As)

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
ppPat (Expl, p) = ppPat' p
ppPat (Impl, p) = braces (ppPat' p)

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
ppRed x (_As, ps, rhs) = ppRedCtx x _As // ppRed' x (ps, rhs)

ppRed' :: PName -> Clause -> Box
ppRed' x (ps, rhs) = ppPName x <+> ppPats ps <+> ppRHS rhs

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

code :: Box -> Box
code d =  char '`' <> d <> char '\''

brackets :: Box -> Box
brackets d = char '[' <> d <> char ']'

textc :: String -> Box
textc x = text x <> char ':'

oft :: Box
oft = char ':'

arr :: Box
arr = text "->"

eq :: Box
eq = text "=="

neq :: Box
neq = text "!="

def :: Box
def = char '='

ndef :: Box
ndef = text "!="

forced :: Box
forced = char '*'

hole :: Box
hole = char '?'

line :: Box
line = text (take 30 (repeat '-'))

newline :: Box
newline = char '\n'

vcatmaybes :: [Maybe Box] -> Box
vcatmaybes = vsep 1 left . catMaybes

vcatmap :: (a -> Box) -> [a] -> Box
vcatmap f xs = vsep 1 left (map f xs)

vcatmap0 :: (a -> Box) -> [a] -> Box
vcatmap0 f xs = vsep 0 left (map f xs)

hcatmap :: (a -> Box) -> [a] -> Box
hcatmap f xs = hsep 1 top (map f xs)

----------------------------------------------------------------------