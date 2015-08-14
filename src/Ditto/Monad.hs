module Ditto.Monad where
import Ditto.Syntax
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.Except
import Data.List

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
extCtx x _A r = r { ctx = (x , _A) : ctx r }

gensym :: TCM Name
gensym = do
  state@DittoS {nameId = nameId} <- get
  let nameId' = succ nameId
  put state { nameId = nameId' }
  return $ "$x" ++ show nameId'

addSig :: Sigma -> TCM ()
addSig s = do
  state@DittoS {sig = sig} <- get
  put state { sig = s : sig }

addDef :: Name -> Exp -> Exp -> TCM ()
addDef x a _A = do
  DittoS {sig = sig} <- get
  when (any (isNamed x) sig) $ throwError
    $ "Definition with name already exists: " ++ show x
  addSig (Def x a _A)

addForm :: PName -> Tel -> TCM ()
addForm x _Is = do
  DittoS {sig = sig} <- get
  when (any (isPNamed x) sig) $ throwError
    $ "Type former with name already exists: " ++ show x
  addSig (DForm x _Is)
  addDef (fromPName x) (lams _Is (Form x (varNames _Is))) (formType _Is)

addCon :: (PName, Tel, PName, [Exp]) -> TCM ()
addCon (x, _As, _X, _Is) = do
  DittoS {sig = sig} <- get
  when (any (isPNamed x) sig) $ throwError
    $ "Constructor with name already exists: " ++ show x
  addSig (DCon x _As _X _Is)
  addDef (fromPName x) (lams _As (Con x (varNames _As))) (pis _As $ Form _X _Is)

----------------------------------------------------------------------

isNamed :: Name -> Sigma -> Bool
isNamed x (Def y _ _) = x == y
isNamed x (DForm y _) = False
isNamed x (DCon y _ _ _) = False
isNamed x (DRed y _) = False

isPNamed :: PName -> Sigma -> Bool
isPNamed x (Def y _ _) = False
isPNamed x (DForm y _) = x == y
isPNamed x (DCon y _ _ _) = x == y
isPNamed x (DRed y _) = x == y

envDef :: Sigma -> Maybe Exp
envDef (Def _ a _) = Just a
envDef _ = Nothing

envType :: Sigma -> Exp
envType (Def _ _ _A) = _A
envType (DForm _ _Is) = formType _Is
envType (DCon _ _As _X _Is) = conType _As _X _Is
envType (DRed _ _) = error "Type of reduction not yet implemented"

----------------------------------------------------------------------

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
