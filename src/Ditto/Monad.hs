module Ditto.Monad where
import Ditto.Syntax
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.Except
import Data.List
import Data.Maybe

----------------------------------------------------------------------

data DittoS = DittoS
  { sig :: [Sigma]
  , nameId :: Integer
  }

data DittoR = DittoR
  { ctx :: Tel
  }

type TCM = StateT DittoS (ReaderT DittoR (ExceptT String Identity))

runTCM :: TCM a -> Either String a
runTCM = runIdentity
  . runExceptT
  . flip runReaderT initialR
  . flip evalStateT initialS

initialS :: DittoS
initialS = DittoS
  { sig = []
  , nameId = 0
  }

initialR :: DittoR
initialR = DittoR
  { ctx = []
  }

extCtx :: Name -> Exp -> DittoR -> DittoR
extCtx x _A r = extCtxs [(x, _A)] r

extCtxs :: Tel -> DittoR -> DittoR
extCtxs _As r = r { ctx = _As ++ ctx r }

gensymHint :: Name -> TCM Name
gensymHint x = do
  state@DittoS {nameId = nameId} <- get
  let nameId' = succ nameId
  put state { nameId = nameId' }
  return $ uniqName x nameId'

addSig :: Sigma -> TCM ()
addSig s = do
  state@DittoS {sig = sig} <- get
  when (s `elem` sig) $ throwError $
    "Element being added already exists in the environment: " ++ show s
  put state { sig = s : sig }

updateSig :: Sigma -> Sigma -> TCM ()
updateSig s s' = do
  state@DittoS {sig = sig} <- get
  case break (== s) sig of
    (sig1, _:sig2) -> put state { sig = sig1 ++ s':sig2 }
    (sig1, []) -> throwError $
      "Element being updated does not exist in the environment: " ++ show s

addDef :: Name -> Exp -> Exp -> TCM ()
addDef x a _A = do
  DittoS {sig = sig} <- get
  when (any (isNamed x) sig) $ throwError
    $ "Definition name already exists in the environment: " ++ show x
  addSig (Def x a _A)

addForm :: PName -> Tel -> TCM ()
addForm x _Is = do
  DittoS {sig = sig} <- get
  when (any (isPNamed x) sig) $ throwError
    $ "Type former name already exists in the environment: " ++ show x
  addSig (DForm x _Is)
  addDef (pname2name x) (lams _Is (Form x (varNames _Is))) (formType _Is)

addCon :: (PName, Tel, PName, [Exp]) -> TCM ()
addCon (x, _As, _X, _Is) = do
  DittoS {sig = sig} <- get
  when (any (isPNamed x) sig) $ throwError
    $ "Constructor name already exists in the environment: " ++ show x
  addSig (DCon x _As _X _Is)
  addDef (pname2name x) (lams _As (Con x (varNames _As))) (pis _As $ Form _X _Is)

addRedType :: PName -> Tel -> Exp -> TCM ()
addRedType x _As _B = do
  DittoS {sig = sig} <- get
  when (any (isPNamed x) sig) $ throwError
    $ "Reduction name already exists in the environment: " ++ show x
  addSig (DRed x [] _As _B)
  addDef (pname2name x) (lams _As (Red x (varNames _As))) (pis _As _B)

addRedClauses :: PName -> [CheckedClause] -> TCM ()
addRedClauses x cs = do
  DittoS {sig = sig} <- get
  case find (isPNamed x) sig of
    Just s@(DRed _ [] _As _B) -> do
      updateSig s (DRed x cs _As _B)
    Just s@(DRed _ _ _As _B) -> throwError $
      "Reduction already contains clauses: " ++ show x
    _ -> throwError $
      "Reduction does not exist in the environment: " ++ show x

----------------------------------------------------------------------

isNamed :: Name -> Sigma -> Bool
isNamed x (Def y _ _) = x == y
isNamed x (DForm y _) = False
isNamed x (DCon y _ _ _) = False
isNamed x (DRed y _ _ _) = False

isPNamed :: PName -> Sigma -> Bool
isPNamed x (Def y _ _) = False
isPNamed x (DForm y _) = x == y
isPNamed x (DCon y _ _ _) = x == y
isPNamed x (DRed y _ _ _) = x == y

isConOf :: PName -> Sigma -> Bool
isConOf x (DCon _ _ y _) = x == y
isConOf x _ = False

envDef :: Sigma -> Maybe Exp
envDef (Def _ a _) = Just a
envDef _ = Nothing

conSig :: Sigma -> Maybe (PName, Tel, [Exp])
conSig (DCon x _As _ is) = Just (x, _As, is)
conSig _ = Nothing

redClauses :: Sigma -> Maybe [CheckedClause]
redClauses (DRed x cs _ _) = Just cs
redClauses _ = Nothing

envType :: Sigma -> Exp
envType (Def _ _ _A) = _A
envType (DForm _ _Is) = formType _Is
envType (DCon _ _As _X _Is) = conType _As _X _Is
envType (DRed _ _ _As _B) = error "Type of reduction not yet implemented"

----------------------------------------------------------------------

lookupCons :: PName -> TCM [(PName, Tel, [Exp])]
lookupCons x = do
  DittoS {sig = sig} <- get
  return . catMaybes . map conSig . filter (isConOf x) $ sig

lookupRedClauses :: PName -> TCM (Maybe [CheckedClause])
lookupRedClauses x = do
  DittoS {sig = sig} <- get
  return $ redClauses =<< find (isPNamed x) sig

lookupDef :: Name -> TCM (Maybe Exp)
lookupDef x = do
  DittoS {sig = sig} <- get
  return $ envDef =<< find (isNamed x) sig

lookupType :: Name -> TCM (Maybe Exp)
lookupType x = do
  DittoS {sig = sig} <- get
  return $ return . envType =<< find (isNamed x) sig

lookupPType :: PName -> TCM (Maybe Exp)
lookupPType x = do
  DittoS {sig = sig} <- get
  return $ return . envType =<< find (isPNamed x) sig

lookupCtx :: Name -> TCM (Maybe Exp)
lookupCtx x = do
  DittoR {ctx = ctx} <- ask
  maybe (return $ lookup x ctx) (return . Just) =<< lookupType x

----------------------------------------------------------------------
