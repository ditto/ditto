module Ditto.Pretty
  ( ppCtxErr
  , ppCtxHoles
  , ppExp
  , render
  , idRen
  ) where
import Ditto.Syntax
import Data.Maybe
import Data.List hiding ( group )
import Text.PrettyPrint.Leijen

----------------------------------------------------------------------

nameFor :: [Name] -> Name -> Name
nameFor xs (namesFor -> ys) = fromJust (find (flip notElem xs) ys)

namesFor :: Name -> [Name]
namesFor (Name e x _) = s2n e x : map (\n -> s2n e (x ++ show n)) [2..]

domRen :: Ren -> [Name]
domRen = map fst

codRen :: Ren -> [Name]
codRen = map snd

extRen :: Ren -> Name -> Ren
extRen ren x = snoc ren (x, nameFor (codRen ren) x)

idRen :: [Name] -> Ren
idRen = map (\x -> (x, x))

telRen :: Ren -> Tel -> Ren
telRen ren (names -> xs) = foldl extRen ren xs

patsRen :: Ren -> Pats -> Ren
patsRen ren (fvPats -> xs) = foldl extRen ren xs

accRen :: Ren -> Ren
accRen = map (\(x, y) -> (x, toAcc y))
  where
  toAcc :: Name -> Name
  toAcc (Name _ x n) = Name Acc x n

----------------------------------------------------------------------

ppErr :: Ren -> Err -> Doc
ppErr ren (EGen err) = text err
ppErr ren (EConv a b) = text "Terms not convertible"
 <+> code (ppExp ren a <+> nconv <+> ppExp ren b)
ppErr ren (EAtom a) = text "Inferring non-atomic term"
 <+> code (ppExp ren a)
ppErr ren (EScope x) = text "Variable not in scope"
  <+> code (ppName ren x)
ppErr ren (ECaseless x) = text "Variable is not caseless"
  <+> code (ppName ren x)
ppErr ren (EMetas xs) = text "Unsolved metavariables" //
  vcatmap1 (\(x, _As, _B) -> ppMetaType ren x _As _B) xs
ppErr ren (ECover _As x qs) = text "Uncovered clause"
  <+> code (ppPName x <+> vcat0 (ppPats VCore (telRen ren _As) qs))
ppErr ren (EReach x xs) = text "Unreachable clauses" //
  vcatmap0 (ppRed' ren x) xs
ppErr ren (ESplit cs) = text "Clauses after split" //
  vcatmap0 (ppSplitting ren) cs

ppCtxErr :: Verbosity -> [Name] -> Prog -> Acts -> Tel -> Err -> Doc
ppCtxErr verb (idRen -> ren) env acts ctx err = vcatmaybes
  [ Just (ppErr (telRen ren ctx) err)
  , ppActs ren acts
  , ppCtx ren ctx
  , ppEnvVerb verb ren env
  ]

----------------------------------------------------------------------

ppCtx :: Ren -> Tel -> Maybe Doc
ppCtx ren [] = Nothing
ppCtx ren xs = Just $ sec "Context" // vcat0 (ppCtxBinds ren xs)

ppEnvVerb :: Verbosity -> Ren -> Prog -> Maybe Doc
ppEnvVerb Normal ren env = Nothing
ppEnvVerb Verbose ren env = ppEnv ren env

ppEnv :: Ren -> Prog -> Maybe Doc
ppEnv ren [] = Nothing
ppEnv ren xs = Just $ sec "Environment" // vcatmap1 (ppStmt ren) xs

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
ppAct ren (AConv x y) = while "equating" $ ppExp ren x <+> conv <+> ppExp ren y
ppAct ren (ACover x qs) = while "covering" $ ppPName x <+> hcat1 (ppPats VCore ren qs)

while :: String -> Doc -> Doc
while str x = text "...while" <+> text str <+> code x

----------------------------------------------------------------------

ppCtxHoles :: Verbosity -> [Name] -> Prog -> Holes -> Doc
ppCtxHoles verb (idRen -> ren) env xs = vcatmaybes [holes, envVerb]
  where
  holes = ppHoles ren xs
  envVerb = ppEnvVerb verb ren env

ppHoles :: Ren -> Holes -> Maybe Doc
ppHoles ren [] = Nothing
ppHoles ren xs = Just $ vcatmap1 (ppHole ren) xs

ppHole :: Ren -> Hole -> Doc
ppHole ren (x, a, _As, _B) =
  (text "Hole" <+> ppMName x <+> oft <+> ppExp (telRen ren _As) _B)
  // dashes <> softappl (vcat0 . ppCtxBinds ren) _As

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
ppInfer (MHole Nothing) = qmark
ppInfer (MHole (Just x)) = qmark <> text x

ppPrim :: Ren -> Wrap -> PName -> Args -> Doc
ppPrim ren w x [] = ppPName x
ppPrim ren w x as = lefty w $ ppPName x <+> hcatmap1 (ppArg ren) as

ppMeta :: Ren -> Wrap -> MName -> Args -> Doc
ppMeta ren w x [] = ppMName x
ppMeta ren w x as = lefty w $ ppMName x <+> hcatmap1 (ppArg ren) as

----------------------------------------------------------------------

ppExpType :: Ren -> Exp -> Doc
ppExpType ren _A@(Pi _ _ _) = ppExp ren _A
ppExpType ren _A = oft <+> ppExp ren _A

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

data Visbility = VCore | VSurface

ppPat :: Visbility -> Ren -> (Icit, Pat) -> Doc
ppPat vis ren (Expl, p) = ppPat' vis ren p
ppPat vis ren (Impl, p) = softindent . braces $ ppPat' vis ren p

ppPat' :: Visbility -> Ren -> Pat -> Doc
ppPat' VCore ren (PVar x) = ppName ren x
ppPat' VSurface ren (PVar x) = ppName (accRen ren) x
ppPat' VCore ren (PInacc Nothing) = forced
ppPat' VCore ren (PInacc (Just a)) = brackets (ppExp ren a)
ppPat' VSurface ren (PInacc _) = forced
ppPat' vis ren (PCon x (ppPats vis ren -> [])) = ppPName x
ppPat' vis ren (PCon x (ppPats vis ren -> ps)) = softindent . parens $ ppPName x <+> hcat1 ps

hiddenPat :: Visbility -> (Icit, Pat) -> Bool
hiddenPat VSurface (Impl, PInacc _) = True
hiddenPat VSurface (Impl, PVar x) = isInacc x
hiddenPat vis _ = False

ppPats :: Visbility -> Ren -> Pats -> [Doc]
ppPats vis ren = map (ppPat vis ren) . reject (hiddenPat vis)

----------------------------------------------------------------------

data Wrap = Wrap | NoWrapL | NoWrap

righty :: Wrap -> Doc -> Doc
righty NoWrap = id
righty _ = softindent . parens

lefty :: Wrap -> Doc -> Doc
lefty Wrap = softindent . parens
lefty _ = id

----------------------------------------------------------------------

ppPrimType :: Ren -> PName -> Exp -> Doc
ppPrimType ren x _A = ppPName x <+> ppExpType ren _A

ppCon :: Ren -> (PName, Exp) -> Doc
ppCon ren (x, _A) = bar <+> ppPrimType ren x _A

ppDataBod :: Ren -> Cons -> Doc
ppDataBod ren [] = end
ppDataBod ren cs = vcatmap0 (ppCon ren) cs // end

----------------------------------------------------------------------

ppRedBod :: Ren -> [Clause] -> Doc
ppRedBod ren [] = end
ppRedBod ren cs = vcatmap0 (ppClause ren) cs // end

ppClause :: Ren -> Clause -> Doc
ppClause ren (ps, rhs) = bar
  <+> hcat1 (ppPats VCore ren' ps)
  <@> ppRHS ren' rhs
  where ren' = patsRen ren ps

ppSplitting :: Ren -> CheckedClause -> Doc
ppSplitting ren (_As, ps, rhs) = bar
  <+> hcat1 (ppPats VSurface ren' ps)
  <@> ppRHS ren' rhs
  where ren' = telRen ren _As

----------------------------------------------------------------------

ppStmt :: Ren -> Stmt -> Doc
ppStmt ren (SData x _A cs) = dayta
  <+> ppPrimType ren x _A
  <+> wear
  // ppDataBod ren cs
ppStmt ren (SDefn x _A cs) = def
  <+> ppPrimType ren x _A
  <+> wear
  // ppRedBod ren cs
ppStmt ren (SDef x a _A) = def
  <+> ppDefType ren x _A
  <+> wear
  // ppExp ren a
  // end
ppStmt ren (SMeta x a _A) = def
  <+> ppMetaType' ren x _A
  <+> wear
  // maybe qmark (ppExp ren) a
  // end

----------------------------------------------------------------------

ppRed :: Ren -> PName -> CheckedClause -> Doc
ppRed ren x (_As, ps, rhs) = ppRedTel ren x _As // ppRed' (telRen ren _As) x (ps, rhs)

ppRed' :: Ren -> PName -> Clause -> Doc
ppRed' ren x (ps, rhs) = ppPName x <+> hcat1 (ppPats VCore ren ps) <@> ppRHS ren rhs

ppRHS :: Ren -> RHS -> Doc
ppRHS ren (Prog a) = eq <+> ppExp ren a
ppRHS ren (Caseless x) = neq <+> ppName ren x
ppRHS ren (Split x) = at <+> ppName ren x

ppRedTel :: Ren -> PName -> Tel -> Doc
ppRedTel ren x _As = ppPName x <+> hcat1 (ppTelBinds ren _As)

--------------------------------------------------------------------------------

ppDMeta :: Ren -> MName -> Maybe Exp -> Tel -> Exp -> Doc
ppDMeta ren x b _As _B = case b of
  Nothing -> ppMetaType ren x _As _B
  Just b -> ppMetaType ren x _As _B // ppMetaBod ren x b

ppMetaType :: Ren -> MName -> Tel -> Exp -> Doc
ppMetaType ren x _As@(_:_) _B = ppMName x <+> ppExp ren (pis _As _B)
ppMetaType ren x [] _B = ppMName x <+> oft <+> ppExp ren _B

ppMetaType' :: Ren -> MName -> Exp -> Doc
ppMetaType' ren x _A = ppMName x <+> ppExpType ren _A

ppMetaBod :: Ren -> MName -> Exp -> Doc
ppMetaBod ren x a = ppMName x <+> eq <+> ppExp ren a

----------------------------------------------------------------------

ppDefType :: Ren -> Name -> Exp -> Doc
ppDefType ren x _A = ppName ren x <+> ppExpType ren _A

----------------------------------------------------------------------

ppName :: Ren -> Name -> Doc
ppName ren x = text . show $ maybe x id (lookup x (reverse ren))

ppPName :: PName -> Doc
ppPName (PName x) = text x

ppMName :: MName -> Doc
ppMName = text . show

----------------------------------------------------------------------

code :: Doc -> Doc
code =  enclose (char '`') squote

textc :: String -> Doc
textc x = text x <> colon

oft :: Doc
oft = colon

arr :: Doc
arr = text "->"

conv :: Doc
conv = text "=="

nconv :: Doc
nconv = text "!="

def :: Doc
def = text "def"

dayta :: Doc
dayta = text "data"

wear :: Doc
wear = text "where"

end :: Doc
end = text "end"

eq :: Doc
eq = char '='

neq :: Doc
neq = text "!="

forced :: Doc
forced = char '*'

qmark :: Doc
qmark = char '?'

bar :: Doc
bar = char '|'

at :: Doc
at = char '@'

dashes :: Doc
dashes = text (take 30 (repeat '-'))

----------------------------------------------------------------------

(<@>) :: Doc -> Doc -> Doc
x <@> y = x <> group (nest 2 line) <> y

softappl :: ([a] -> Doc) -> [a] -> Doc
softappl f [] = empty
softappl f xs = line <> f xs

softappr :: ([a] -> Doc) -> [a] -> Doc
softappr f [] = empty
softappr f xs = f xs <> line

softindent :: Doc -> Doc
softindent x = group (nest 2 linebreak) <> x

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
vcatmaybes = softappr vcat1 . catMaybes

vcatmap1 :: (a -> Doc) -> [a] -> Doc
vcatmap1 f xs = vcat1 (map f xs)

vcatmap0 :: (a -> Doc) -> [a] -> Doc
vcatmap0 f xs = vcat0 (map f xs)

hcatmap1 :: (a -> Doc) -> [a] -> Doc
hcatmap1 f xs = hcat1 (map f xs)

render :: Doc -> String
render doc = displayS (renderPretty 0.4 300 doc) ""

----------------------------------------------------------------------
