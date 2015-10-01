module Ditto.Pretty where
import Ditto.Syntax
import Data.Maybe
import Data.List hiding ( group )
import Text.PrettyPrint.Leijen

----------------------------------------------------------------------

nameFor :: [Name] -> Name -> Name
nameFor xs (namesFor -> ys) = fromJust (find (flip notElem xs) ys)

namesFor :: Name -> [Name]
namesFor (Name x _) = s2n x : map (\n -> s2n (x ++ show n)) [2..]

domRen :: Ren -> [Name]
domRen = map fst

codRen :: Ren -> [Name]
codRen = map snd

extRen :: Ren -> Name -> Ren
extRen ren x = snoc ren (x, nameFor (codRen ren) x)

envRen :: Env -> Ren
envRen = idRen . defNames

idRen :: [Name] -> Ren
idRen = map (\x -> (x, x))

telRen :: Ren -> Tel -> Ren
telRen ren (names -> xs) = foldl extRen ren xs

----------------------------------------------------------------------

ppErr :: Ren -> Err -> Doc
ppErr ren (EGen err) = text err
ppErr ren (EConv a b) = text "Terms not convertible"
 <+> code (ppExp ren a <+> neq <+> ppExp ren b)
ppErr ren (EScope x) = text "Variable not in scope"
  <+> code (ppName ren x)
ppErr ren (ECaseless x) = text "Variable is not caseless"
  <+> code (ppName ren x)
ppErr ren (EMetas xs) = text "Unsolved metavariables" //
  vcatmap1 (\(x, _As, _B) -> ppMetaType ren x _As _B) xs
ppErr ren (ECover _As x qs) = text "Uncovered clause"
  <+> code (ppPName x <+> vcat0 (ppPats (telRen ren _As) qs))
ppErr ren (EReach x xs) = text "Unreachable clauses" //
  vcatmap1 (ppRed' ren x) xs

ppCtxErr :: Verbosity -> Acts -> Tel -> Env -> Err -> Doc
ppCtxErr verb acts ctx env err = vcatmaybes
  [ Just (ppErr (telRen ren ctx) err)
  , ppActs ren acts
  , ppCtx ren ctx
  , ppEnvVerb verb ren env
  ]
 where ren = envRen env

----------------------------------------------------------------------

ppCtx :: Ren -> Tel -> Maybe Doc
ppCtx ren [] = Nothing
ppCtx ren xs = Just $ sec "Context" // vcat0 (ppCtxBinds ren xs)

ppEnvVerb :: Verbosity -> Ren -> Env -> Maybe Doc
ppEnvVerb Normal ren env = Nothing
ppEnvVerb Verbose ren env = ppEnv ren env

ppEnv :: Ren -> Env -> Maybe Doc
ppEnv ren [] = Nothing
ppEnv ren xs = Just $ sec "Environment" // vcatmap1 (ppSig ren) xs

sec :: String -> Doc
sec str = textc str // dashes

----------------------------------------------------------------------

ppActs :: Ren -> Acts -> Maybe Doc
ppActs ren [] = Nothing
ppActs ren xs = Just $ vcatmap0 (\(ctx, act) -> ppAct (telRen ren ctx) act) xs

ppAct :: Ren -> Act -> Doc
ppAct ren (ADef x) = while "checking definition" $ ppName ren x
ppAct ren (ADefn x) = while "checking function" $ ppPName x
ppAct ren (AData x) = while "checking datatype" $ ppPName x
ppAct ren (ACon x) = while "checking constructor" $ ppPName x

ppAct ren (ACheck a _A) = while "checking" $ ppwExp ren Wrap a <@> oft <+> ppExp ren _A
ppAct ren (AInfer a) = while "inferring" $ ppExp ren a
ppAct ren (AConv x y) = while "equating" $ ppExp ren x <+> eq <+> ppExp ren y
ppAct ren (ACover x qs) = while "covering" $ ppPName x <+> hcat1 (ppPats ren qs)

while :: String -> Doc -> Doc
while str x = text "...while" <+> text str <+> code x

----------------------------------------------------------------------

ppHoles :: Verbosity -> Env -> Holes -> Doc
ppHoles verb env xs = vcatmaybes [Just holes, ppEnvVerb verb ren env]
  where
  ren = envRen env
  holes = vcatmap1 (ppHole ren) xs

ppHole :: Ren -> Hole -> Doc
ppHole ren (x, nm, a, _As, _B) =
  (text "Hole" <+> ppMName x nm <+> oft <+> ppExp (telRen ren _As) _B)
  // dashes // vcat0 (ppCtxBinds ren _As)

----------------------------------------------------------------------

ppExp :: Ren -> Exp -> Doc
ppExp ren = ppwExp ren NoWrap

ppArg :: Ren -> (Icit, Exp) -> Doc
ppArg ren (Expl, a) = ppwExp ren Wrap a
ppArg ren (Impl, a) = braces (ppExp ren a)

ppwExp :: Ren -> Wrap -> Exp -> Doc
ppwExp ren w Type = text "Type"
ppwExp ren w (Infer m) = ppInfer m
ppwExp ren w (Var x) = ppName ren x
ppwExp ren w x@(Pi _ _ _) = righty w (ppPis ren x)
ppwExp ren w x@(Lam _ _ _) = righty w (ppLams ren x)
ppwExp ren w (Form _X _Is) = ppPrim ren w _X _Is
ppwExp ren w (Con x as) = ppPrim ren w x as
ppwExp ren w (Red x as) = ppPrim ren w x as
ppwExp ren w (Meta x as) = ppMeta ren w x as
ppwExp ren w (App i f a) = lefty w $ ppwExp ren NoWrapL f <+> ppArg ren (i, a)

ppInfer :: MKind -> Doc
ppInfer MInfer = forced
ppInfer (MHole nm) = hole nm

ppPrim :: Ren -> Wrap -> PName -> Args -> Doc
ppPrim ren w x [] = ppPName x
ppPrim ren w x as = lefty w $ ppPName x <+> hcatmap1 (ppArg ren) as

ppMeta :: Ren -> Wrap -> MName -> Args -> Doc
ppMeta ren w x [] = ppMName x Nothing
ppMeta ren w x as = lefty w $ ppMName x Nothing <+> hcatmap1 (ppArg ren) as

----------------------------------------------------------------------

ppPis :: Ren -> Exp -> Doc
ppPis ren (Pi i _A (Bind x _B)) = ppTelBind ren (i, x, _A) <@> ppPis (extRen ren x) _B
ppPis ren _B = oft <+> ppExp ren _B

ppLams :: Ren -> Exp -> Doc
ppLams ren (Lam i _A (Bind x b)) = ppTelBind ren (i, x, _A) <@> ppLams (extRen ren x) b
ppLams ren b = arr <+> ppExp ren b

----------------------------------------------------------------------

ppTelBind :: Ren -> (Icit, Name, Exp) -> Doc
ppTelBind ren (i, x, _A) = icit i $ curry (ppCtxBind ren) x _A

ppTelBinds :: Ren -> Tel -> [Doc]
ppTelBinds ren xs = map (uncurry icit) (ppBinds ren xs)

----------------------------------------------------------------------

ppCtxBind :: Ren -> (Name, Exp) -> Doc
ppCtxBind ren (x, _A) = ppName (extRen ren x) x <+> oft <+> ppExp ren _A

ppCtxBinds :: Ren -> Tel -> [Doc]
ppCtxBinds ren xs = map snd (ppBinds ren xs)

----------------------------------------------------------------------

icit :: Icit -> Doc -> Doc
icit Expl = parens
icit Impl = braces

ppBinds :: Ren -> Tel -> [(Icit, Doc)]
ppBinds ren [] = []
ppBinds ren ((i, x, _A):_As) = (i, ppCtxBind ren (x, _A)) : ppBinds (extRen ren x) _As

----------------------------------------------------------------------

ppPat :: Ren -> (Icit, Pat) -> Doc
ppPat ren (Expl, p) = ppPat' ren p
ppPat ren (Impl, p) = softindent . braces $ ppPat' ren p

ppPat' :: Ren -> Pat -> Doc
ppPat' ren (PVar x) = ppName ren x
ppPat' ren (Inacc Nothing) = forced
ppPat' ren (Inacc (Just a)) = text "." <> ppwExp ren Wrap a
ppPat' ren (PCon x []) = ppPName x
ppPat' ren (PCon x ps) = softindent . parens $ ppPName x <+> hcat1 (ppPats ren ps)

ppPats :: Ren -> Pats -> [Doc]
ppPats ren = map (ppPat ren)

----------------------------------------------------------------------

data Wrap = Wrap | NoWrapL | NoWrap

righty :: Wrap -> Doc -> Doc
righty NoWrap = id
righty _ = softindent . parens

lefty :: Wrap -> Doc -> Doc
lefty Wrap = softindent . parens
lefty _ = id

----------------------------------------------------------------------

ppSig :: Ren -> Sigma -> Doc
ppSig ren (Def x a _A) = ppDefType ren x _A // ppDefBod ren x a
ppSig ren (DForm _X _Is) = brackets $ ppPName _X <+> text "type former"
ppSig ren (DCon _Y _As _X _Is) = brackets $ ppPName _Y <+> text "constructor of" <+> ppPName _X
ppSig ren (DRed x cs _As _B) = if null cs then header
  else header /+/ vcatmap1 (ppRed ren x) cs
  where header = brackets (ppPName x <+> text "reduction rules")
ppSig ren (DMeta x _ b _As _B) = ppDMeta ren x b _As _B

----------------------------------------------------------------------

ppRed :: Ren -> PName -> CheckedClause -> Doc
ppRed ren x (_As, ps, rhs) = ppRedTel ren x _As // ppRed' (telRen ren _As) x (ps, rhs)

ppRed' :: Ren -> PName -> Clause -> Doc
ppRed' ren x (ps, rhs) = ppPName x <+> hcat1 (ppPats ren ps) <@> ppRHS ren rhs

ppRHS :: Ren -> RHS -> Doc
ppRHS ren (Prog a) = def <+> ppExp ren a
ppRHS ren (Caseless x) = ndef <+> ppName ren x

ppRedTel :: Ren -> PName -> Tel -> Doc
ppRedTel ren x _As = ppPName x <+> hcat1 (ppTelBinds ren _As)

--------------------------------------------------------------------------------

ppDMeta :: Ren -> MName -> Maybe Exp -> Tel -> Exp -> Doc
ppDMeta ren x b _As _B = case b of
  Nothing -> ppMetaType ren x _As _B
  Just b -> ppMetaType ren x _As _B // ppMetaBod ren x b

ppMetaType :: Ren -> MName -> Tel -> Exp -> Doc
ppMetaType ren x _As@(_:_) _B = ppMName x Nothing <+> ppExp ren (metaType _As _B)
ppMetaType ren x [] _B = ppMName x Nothing <+> oft <+> ppExp ren _B

ppMetaBod :: Ren -> MName -> Exp -> Doc
ppMetaBod ren x a = ppMName x Nothing <+> def <+> ppExp ren a

----------------------------------------------------------------------

ppDefType :: Ren -> Name -> Exp -> Doc
ppDefType ren x _A@(Pi _ _ _) = ppName ren x <+> ppExp ren _A
ppDefType ren x _A = ppName ren x <+> oft <+> ppExp ren _A

ppDefBod :: Ren -> Name -> Exp -> Doc
ppDefBod ren x a = ppName ren x <+> def <+> ppExp ren a

----------------------------------------------------------------------

ppName :: Ren -> Name -> Doc
ppName ren x = text . show $ maybe x id (lookup x (reverse ren))

ppPName :: PName -> Doc
ppPName (PName x) = text x

ppMName :: MName -> Maybe String -> Doc
ppMName n Nothing = text $ show n
ppMName n (Just nm) = text $ show n ++ "-" ++ nm

----------------------------------------------------------------------

code :: Doc -> Doc
code =  enclose (char '`') squote

textc :: String -> Doc
textc x = text x <> colon

oft :: Doc
oft = colon

arr :: Doc
arr = text "->"

eq :: Doc
eq = text "=="

neq :: Doc
neq = text "!="

def :: Doc
def = char '='

ndef :: Doc
ndef = text "!="

forced :: Doc
forced = char '*'

qmark :: Doc
qmark = char '?'

hole :: Maybe String -> Doc
hole Nothing = qmark
hole (Just nm) = qmark <> text nm

dashes :: Doc
dashes = text (take 30 (repeat '-'))

----------------------------------------------------------------------

(<@>) :: Doc -> Doc -> Doc
x <@> y = x <> group (nest 2 line) <> y

softindent :: Doc -> Doc
softindent x = empty <> group (nest 2 linebreak) <> x

(//) :: Doc -> Doc -> Doc
x // y = x <> line <> y

(/+/) :: Doc -> Doc -> Doc
x /+/ y = x <> line <> line <> y

vcat0 :: [Doc] -> Doc
vcat0 = vcat

vcat1 :: [Doc] -> Doc
vcat1 = vcat0 . punctuate line

hcat1 :: [Doc] -> Doc
hcat1 = hcat . punctuate space

vcatmaybes :: [Maybe Doc] -> Doc
vcatmaybes = vcat1 . catMaybes

vcatmap1 :: (a -> Doc) -> [a] -> Doc
vcatmap1 f xs = vcat1 (map f xs)

vcatmap0 :: (a -> Doc) -> [a] -> Doc
vcatmap0 f xs = vcat0 (map f xs)

hcatmap1 :: (a -> Doc) -> [a] -> Doc
hcatmap1 f xs = hcat1 (map f xs)

render :: Doc -> String
render doc = displayS (renderPretty 0.4 300 doc) ""

----------------------------------------------------------------------
