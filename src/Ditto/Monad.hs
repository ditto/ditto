module Ditto.Monad where
import Ditto.Syntax
import Ditto.Pretty
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
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

type TCM = StateT DittoS (ReaderT DittoR (ExceptT String Identity))

runTCM :: Verbosity -> TCM a -> Either String a
runTCM v = runIdentity
  . runExceptT
  . flip runReaderT initialR
  . flip evalStateT initialS {verbosity = v}

runTCMVerbose :: TCM a -> Either String a
runTCMVerbose = runTCM Verbose

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

extCtx :: Icit -> Name -> Exp -> TCM a -> TCM a
extCtx i x _A = extCtxs [(i, x, _A)]

extCtxs :: Tel -> TCM a -> TCM a
extCtxs _As = local (\ r -> r { ctx = ctx r ++ _As })

during :: Act -> TCM a -> TCM a
during x m = do
  ctx <- getCtx
  local (\ r -> r { acts = (ctx, x):acts r }) m

----------------------------------------------------------------------

gensym :: TCM Integer
gensym = do
  state@DittoS {nameId = nameId} <- get
  let nameId' = succ nameId
  put state { nameId = nameId' }
  return nameId'

gensymHint :: Name -> TCM Name
gensymHint x = uniqName x <$> gensym

gensymMeta :: TCM MName
gensymMeta = do
  sym <- gensym
  return $ MName sym

----------------------------------------------------------------------

lookupCons :: PName -> TCM [(PName, Tel, Args)]
lookupCons x = do
  env <- getEnv
  return . catMaybes . map conSig . filter (isConOf x) $ env

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

lookupPSigma :: PName -> TCM (Maybe Sigma)
lookupPSigma x = do
  env <- getEnv
  return $ return =<< find (isPNamed x) env

lookupPType :: PName -> TCM (Maybe Exp)
lookupPType x = do
  s <- lookupPSigma x
  return $ return . envType =<< s

----------------------------------------------------------------------

lookupDefs :: TCM [(Name, Exp, Exp)]
lookupDefs = do
  env <- getEnv
  return . filterDefs $ env

lookupUndefMetas :: TCM [(MName, Tel, Exp)]
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
    return $ Just . envType =<< s

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

renderHoles :: Holes -> TCM String
renderHoles xs = do
  verb <- getVerbosity
  env <- getEnv
  return . render $ ppCtxHoles verb env xs

throwGenErr :: String -> TCM a
throwGenErr = throwErr . EGen

throwErr :: Err -> TCM a
throwErr err = do
  verb <- getVerbosity
  acts <- getActs
  ctx <- getCtx
  env <- getEnv
  throwError . render . ppCtxErr verb acts ctx env $ err

----------------------------------------------------------------------
