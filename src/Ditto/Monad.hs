module Ditto.Monad where
import Ditto.Syntax
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Data.List
import Data.Maybe

----------------------------------------------------------------------

data DittoS = DittoS
  { env :: Env
  , nameId :: Integer
  , verbosity :: Verbosity
  }

data DittoR = DittoR
  { ctx :: Tel
  , acts :: Acts
  }

type TCM = StateT DittoS (ReaderT DittoR (Except CtxErr))

----------------------------------------------------------------------

runTCM :: Verbosity -> TCM a -> Either CtxErr a
runTCM v =
    runExcept
  . flip runReaderT initialR
  . flip evalStateT initialS {verbosity = v}

----------------------------------------------------------------------

initialS :: DittoS
initialS = DittoS
  { env = []
  , nameId = 0
  , verbosity = Normal
  }

initialR :: DittoR
initialR = DittoR
  { ctx = []
  , acts = []
  }

----------------------------------------------------------------------

withinCtx :: Acts -> Tel -> TCM a -> TCM a
withinCtx acts' ctx' = local (\ r -> r { acts = acts' , ctx = ctx' })

extCtx :: Icit -> Name -> Exp -> TCM a -> TCM a
extCtx i x _A = extCtxs [(i, x, _A)]

extCtxs :: Tel -> TCM a -> TCM a
extCtxs _As = local (\ r -> r { ctx = ctx r ++ _As })

----------------------------------------------------------------------

gensym :: TCM Integer
gensym = do
  state@DittoS {nameId = nameId} <- get
  let nameId' = succ nameId
  put state { nameId = nameId' }
  return nameId'

gensymHint :: Name -> TCM Name
gensymHint x = uniqName x <$> gensym

gensymEHint :: Essible -> Name -> TCM Name
gensymEHint e x = uniqEName e x <$> gensym

gensymMeta :: MKind -> TCM MName
gensymMeta k = MName k <$> gensym

gensymGuard :: TCM GName
gensymGuard = GName <$> gensym

----------------------------------------------------------------------

mkProb1 :: Exp -> Exp -> TCM Prob
mkProb1 a1 a2 = do
  acts <- getActs
  ctx <- getCtx
  return $ Prob1 acts ctx a1 a2

mkProbN :: Prob -> Args -> Args -> TCM Prob
mkProbN p [] [] = return p
mkProbN p as1 as2 = do
  acts <- getActs
  ctx <- getCtx
  return $ ProbN p acts ctx as1 as2

----------------------------------------------------------------------

lookupCon :: PName -> TCM (Maybe (ConSig))
lookupCon x = do
  env <- getEnv
  return $ conSig x =<< find (isPNamed x) env

lookupCons :: PName -> TCM (Maybe [ConSig])
lookupCons x = do
  env <- getEnv
  return $ conSigs =<< find (isPNamed x) env

lookupRedType :: PName -> TCM (Maybe (Tel, Exp))
lookupRedType x = do
  env <- getEnv
  return $ redType =<< find (isPNamed x) env

lookupRedClauses :: PName -> TCM (Maybe [CheckedClause])
lookupRedClauses x = do
  env <- getEnv
  return $ redClauses =<< find (isPNamed x) env

----------------------------------------------------------------------

lookupMeta :: MName -> TCM (Maybe Exp)
lookupMeta x = do
  env <- getEnv
  return $ envMetaBody =<< find (isMNamed x) env

lookupMetaType :: MName -> TCM (Maybe (Tel, Exp))
lookupMetaType x = do
  env <- getEnv
  return $ envMetaType =<< find (isMNamed x) env

----------------------------------------------------------------------

lookupGuard :: GName -> TCM (Maybe Exp)
lookupGuard x = do
  env <- getEnv
  return $ envGuardBody =<< find (isGNamed x) env

lookupGuardType :: GName -> TCM (Maybe Exp)
lookupGuardType x = do
  env <- getEnv
  return $ envGuardType =<< find (isGNamed x) env

lookupProb :: GName -> TCM (Maybe Prob)
lookupProb x = do
  env <- getEnv
  return $ envGuardProb =<< find (isGNamed x) env

----------------------------------------------------------------------

lookupPSigma :: PName -> TCM (Maybe Sigma)
lookupPSigma x = do
  env <- getEnv
  return $ return =<< find (isPNamed x) env

----------------------------------------------------------------------

lookupDefs :: TCM [(Name, Maybe Exp, Exp)]
lookupDefs = do
  env <- getEnv
  return . filterDefs $ env

lookupUndefMetas :: TCM Holes
lookupUndefMetas = do
  env <- getEnv
  return . catMaybes . map envUndefMeta . filter isMeta $ env

lookupHoles :: TCM Holes
lookupHoles = do
  env <- getEnv
  return . catMaybes . map envHole . filter isMeta $ env

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
    return $ envDefType =<< s

lookupCtx :: Name -> TCM (Maybe Exp)
lookupCtx x = do
  ctx <- getCtx
  return $ lookupTel x ctx

lookupSigma :: Name -> TCM (Maybe Sigma)
lookupSigma x = do
  env <- getEnv
  return $ return =<< find (isNamed x) env

----------------------------------------------------------------------

getCtx :: TCM Tel
getCtx = do
  DittoR {ctx = ctx} <- ask
  return ctx

getEnv :: TCM Env
getEnv = do
  DittoS {env = env} <- get
  return env

getActs :: TCM Acts
getActs = do
  DittoR {acts = acts} <- ask
  return acts

getVerbosity :: TCM Verbosity
getVerbosity = do
  DittoS {verbosity = verbosity} <- get
  return verbosity

setVerbosity :: Verbosity -> TCM ()
setVerbosity v = do
  state@DittoS{} <- get
  put state { verbosity = v }

----------------------------------------------------------------------
