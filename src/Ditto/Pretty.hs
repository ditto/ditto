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
ppErr ren (EUnsolved ps hs) = text "Unsolved metavariables and constraints" //
  ppUnsolved ren ps hs
ppErr ren (ECover _As x qs) = text "Uncovered clause"
  <+> code (ppPName x <+> vcat0 (ppPats VCore (telRen ren _As) qs))
ppErr ren (EReach x xs) = text "Unreachable clauses" //
  vcatmap0 (ppRed' ren x) xs
ppErr ren (ESplit cs) = text "Clauses after split" //
  vcatmap0 (ppSplitting ren) cs

ppCtxErr :: Verbosity -> [Name] -> Prog -> Acts -> Tel -> Err -> Doc
ppCtxErr verb (idRen -> ren) env acts ctx err = vcatmaybes
  [ Just (ppErr (telRen ren ctx) err)
  , ppActsM ren acts
  , ppCtxM ren ctx
  , ppEnvVerbM verb ren env
  ]

----------------------------------------------------------------------

ppCtxM :: Ren -> Tel -> Maybe Doc
ppCtxM ren [] = Nothing
ppCtxM ren xs = Just $ sec "Context" // ppCtx ren xs

ppCtx :: Ren -> Tel -> Doc
ppCtx ren xs = vcat0 (ppCtxBinds ren xs)

ppEnvVerbM :: Verbosity -> Ren -> Prog -> Maybe Doc
ppEnvVerbM Normal ren env = Nothing
ppEnvVerbM Verbose ren env = ppEnvM ren env

ppEnvM :: Ren -> Prog -> Maybe Doc
ppEnvM ren [] = Nothing
ppEnvM ren xs = Just $ sec "Environment" // vcatmap1 (ppStmt ren) (forget xs)
  where
  forget :: Prog -> [Stmt]
  forget [] = []
  forget (Left d:ds) = d : forget ds
  forget (Right ds:es) = ds ++ forget es

sec :: String -> Doc
sec str = textc str // dashes

----------------------------------------------------------------------

ppActsM :: Ren -> Acts -> Maybe Doc
ppActsM ren [] = Nothing
ppActsM ren xs = Just $ ppActs ren xs

ppActs :: Ren -> Acts -> Doc
ppActs ren xs = vcatmap0 (\(ctx, act) -> ppAct (telRen ren ctx) act) xs

ppAct :: Ren -> Act -> Doc
ppAct ren (ADef x) = while "checking definition" $ ppName ren x
ppAct ren (ADefn x) = while "checking function" $ ppPName x
ppAct ren (AData x) = while "checking datatype" $ ppPName x
ppAct ren (ACon x) = while "checking constructor" $ ppPName x

ppAct ren (ACheck a _A) = while "checking" $ ppExp ren a <@> oft2 <+> ppExp ren _A
ppAct ren (AInfer a) = while "inferring" $ ppExp ren a
ppAct ren (AConv x y) = while "equating" $ ppExp ren x <+> conv <+> ppExp ren y
ppAct ren (ACover x qs) = while "covering" $ ppPName x <+> hcat1 (ppPats VCore ren qs)

while :: String -> Doc -> Doc
while str x = text "...while" <+> text str <+> code x

----------------------------------------------------------------------

ppCtxHoles :: Verbosity -> [Name] -> Prog -> Holes -> Doc
ppCtxHoles verb (idRen -> ren) env xs = vcatmaybes [holes, envVerb]
  where
  holes = ppHolesM ren xs
  envVerb = ppEnvVerbM verb ren env

ppHolesM :: Ren -> Holes -> Maybe Doc
ppHolesM ren [] = Nothing
ppHolesM ren xs = Just $ vcatmap1 (ppHole ren) xs

ppHole :: Ren -> Hole -> Doc
ppHole ren (x, acts, ctx, _A) =
  (text label <+> ppMName x <+> oft <+> ppExp (telRen ren ctx) _A)
  // dashes <> softappl (ppCtx ren) ctx <> softappl (ppActs ren) acts
  where label = if isHole x then "Hole" else "Meta"

----------------------------------------------------------------------

ppUnsolved :: Ren -> [Prob] -> Holes -> Doc
ppUnsolved ren xs ys = vcat1 (map (ppProb ren) xs ++ map (ppHole ren) ys)

ppProb :: Ren -> Prob -> Doc
ppProb ren (Prob1 acts ctx a1 a2) =
  (ppExp (telRen ren ctx) a1 <+> nconv <+> ppExp (telRen ren ctx) a2)
  // dashes <> softappl (ppCtx ren) ctx <> softappl (ppActs ren) acts
ppProb ren (ProbN p _ _ _ _) = ppProb ren p

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
ppwExp ren w (Guard x) = ppGuard ren w x
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

ppGuard :: Ren -> Wrap -> GName -> Doc
ppGuard ren w x = ppGName x

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

----------------------------------------------------------------------

ppRed :: Ren -> PName -> CheckedClause -> Doc
ppRed ren x (_As, ps, rhs) = ppRedTel ren x _As // ppRed' (telRen ren _As) x (ps, rhs)

ppRed' :: Ren -> PName -> Clause -> Doc
ppRed' ren x (ps, rhs) = ppPName x <+> hcat1 (ppPats VCore ren ps) <@> ppRHS ren rhs

ppRHS :: Ren -> RHS -> Doc
ppRHS ren (MapsTo a) = eq <+> ppExp ren a
ppRHS ren (Caseless x) = neq <+> ppName ren x
ppRHS ren (Split x) = at <+> ppName ren x

ppRedTel :: Ren -> PName -> Tel -> Doc
ppRedTel ren x _As = ppPName x <+> hcat1 (ppTelBinds ren _As)

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

ppGName :: GName -> Doc
ppGName = text . show

----------------------------------------------------------------------

code :: Doc -> Doc
code =  enclose (char '`') squote

textc :: String -> Doc
textc x = text x <> colon

oft :: Doc
oft = colon

oft2 :: Doc
oft2 = colon <> colon

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
