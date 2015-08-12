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
extCtx x _A r = r { ctx = (x , _A) : ctx r }

gensym :: TCM Name
gensym = gensymHint "x"

gensymP :: TCM PName
gensymP = undefined

gensymPHint :: String -> TCM PName
gensymPHint x = undefined

gensymHint :: String -> TCM Name
gensymHint x = do
  state@DittoS {nameId = nameId} <- get
  let nameId' = succ nameId
  put state { nameId = nameId' }
  return $ "$" ++ x ++ show nameId'

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

addElim :: PName -> TCM ()
addElim _X = do
  (_Is, _Cs) <- lookupForElim _X
  t <- gensymHint "t"  -- target name
  _P <- gensymHint "P" -- motive name
  _Cs' <- mapM (\(c, _As, is) -> do n <- gensymHint ("m"++ fromPName c)
                                    return (n , c, _As, is))_Cs
  -- type of the eliminator
  let (etel, res) = elimType _X (t, _P, _Is, _Cs')
  -- body of the eliminator
  let a = lams etel (Elim _X $ varNames etel)
  -- add the delta equivalent term it would be nice to type-check
  -- this, but the check module uses this one, so one can't call it
  -- from here
  addDef ("elim" ++ fromPName _X) a (pis etel res)


----------------------------------------------------------------------

data Normality = BetaDelta | Rho
data Lookup = LDef | LType

isNamed :: Name -> Sigma -> Bool
isNamed x (Def y _ _) = x == y
isNamed x (Virt y _ _) = x == y
isNamed x (DForm y _) = False
isNamed x (DCon y _ _ _) = False

isPNamed :: PName -> Sigma -> Bool
isPNamed x (Def y _ _) = False
isPNamed x (Virt y _ _) = False
isPNamed x (DForm y _) = x == y
isPNamed x (DCon y _ _ _) = x == y

conOf :: PName -> Sigma -> Maybe (PName, Tel, [Exp])
conOf _X (DCon x _As _Y _Is) | _X == _Y = Just (x, _As, _Is)
conOf _X _ = Nothing

envDef :: Normality -> Sigma -> Maybe Exp
envDef n (Def _ a _) = Just a
envDef Rho (Virt _ a _) = Just a
envDef _ _ = Nothing

envType :: Sigma -> Exp
envType (Def _ _ _A) = _A
envType (Virt _ _ _A) = _A
envType (DForm _ _Is) = formType _Is
envType (DCon _ _As _X _Is) = conType _As _X _Is

----------------------------------------------------------------------

lookupDef :: Normality -> Name -> TCM (Maybe Exp)
lookupDef n x = do
  DittoS {sig = sig} <- get
  return $ envDef n =<< find (isNamed x) sig

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

-- Former index types
-- List of: Constructor name, constructor argument types,
--   and constructor former indices
lookupForElim :: PName -> TCM (Tel, [(PName, Tel, [Exp])])
lookupForElim _X = do
  DittoS {sig = sig} <- get
  case find (isPNamed _X) sig of
    Just (DForm _ _Is) -> do
      let _Cs = mapMaybe (conOf _X) sig
      return (_Is , _Cs)
    otherwise -> throwError "Type former not found"

----------------------------------------------------------------------
