{-# LANGUAGE LambdaCase #-}
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

extCtx :: Name -> Exp -> TCM a -> TCM a
extCtx x _A = extCtxs [(x, _A)]

-- telescopes are in legible order, so reverse them
extCtxs :: Tel -> TCM a -> TCM a
extCtxs _As = local (\ r -> r { ctx = reverse _As ++ ctx r })

gensymHint :: Name -> TCM Name
gensymHint x = do
  state@DittoS {nameId = nameId} <- get
  let nameId' = succ nameId
  put state { nameId = nameId' }
  return $ uniqName x nameId'

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

isDef :: Sigma -> Bool
isDef (Def _ _ _) = True
isDef _ = False

envDef :: Sigma -> Maybe (Name, Exp, Exp)
envDef (Def x a _A) = Just (x, a, _A)
envDef _ = Nothing

envDefBody :: Sigma -> Maybe Exp
envDefBody (Def _ a _) = Just a
envDefBody _ = Nothing

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

----------------------------------------------------------------------

lookupPSigma :: PName -> TCM (Maybe Sigma)
lookupPSigma x = do
  DittoS {sig = sig} <- get
  return $ return =<< find (isPNamed x) sig

lookupPType :: PName -> TCM (Maybe Exp)
lookupPType x = do
  s <- lookupPSigma x
  return $ return . envType =<< s

----------------------------------------------------------------------

lookupDefs :: TCM [(Name, Exp, Exp)]
lookupDefs = do
  DittoS {sig = sig} <- get
  return . catMaybes . map envDef . filter isDef $ sig

----------------------------------------------------------------------

lookupDef :: Name -> TCM (Maybe Exp)
lookupDef x = lookupCtx x >>= \case
  Just _ -> return Nothing
  Nothing -> do
    s <- lookupSigma x
    return $ envDefBody =<< s

lookupType :: Name -> TCM (Maybe Exp)
lookupType x = lookupCtx x >>= \case
  Just _A -> return . Just $ _A
  Nothing -> do
    s <- lookupSigma x
    return $ Just . envType =<< s

lookupCtx :: Name -> TCM (Maybe Exp)
lookupCtx x = do
  DittoR {ctx = ctx} <- ask
  return $ lookup x ctx

lookupSigma :: Name -> TCM (Maybe Sigma)
lookupSigma x = do
  DittoS {sig = sig} <- get
  return $ return =<< find (isNamed x) sig

----------------------------------------------------------------------
