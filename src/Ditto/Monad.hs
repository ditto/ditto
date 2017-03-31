module Ditto.Monad where
import Ditto.Syntax
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Data.List
import Data.Maybe
import qualified Data.Map as Map

----------------------------------------------------------------------

data DittoS = DittoS
  { env :: Env
  , probs :: Probs
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

anyM :: MonadError e m => (a -> m b) -> [a] -> m b
anyM f (x:[]) = f x
anyM f (x:xs) = catchError (f x) (const (anyM f xs))
anyM f [] = error "anyM applied to empty list"

----------------------------------------------------------------------

initialS :: DittoS
initialS = DittoS
  { env = []
  , probs = Map.empty
  , nameId = 0
  , verbosity = Normal
  }

initialR :: DittoR
initialR = DittoR
  { ctx = []
  , acts = []
  }

----------------------------------------------------------------------

resetCtx :: Acts -> Tel -> TCM a -> TCM a
resetCtx acts' ctx' = local (\ r -> r { acts = acts' , ctx = ctx' })

extCtx :: Icit -> Name -> Exp -> TCM a -> TCM a
extCtx i x _A = extCtxs [(i, x, _A)]

extCtxs :: Tel -> TCM a -> TCM a
extCtxs _As = local (\ r -> r { ctx = ctx r ++ _As })

----------------------------------------------------------------------

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

gensymEHint :: Essible -> Name -> TCM Name
gensymEHint e x = uniqEName e x <$> gensym

gensymInacc :: TCM Name
gensymInacc = gensymHint (s2n Inacc "x")

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

lookupRedClauses :: PName -> TCM (Maybe CheckedClauses)
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
lookupGuard x = lookupProb x >>= \case
  Just _ -> return Nothing
  Nothing -> do
    env <- getEnv
    return $ envGuardBody =<< find (isGNamed x) env

lookupGuardType :: GName -> TCM (Maybe Exp)
lookupGuardType x = do
  env <- getEnv
  return $ envGuardType =<< find (isGNamed x) env

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
lookupDef x = do
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
getEnv = env <$> get

----------------------------------------------------------------------

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

getProbs :: TCM Probs
getProbs = probs <$> get

setProbs :: Probs -> TCM ()
setProbs ps = do
  state <- get
  put state { probs = ps }

lookupProb :: GName -> TCM MProb
lookupProb x = do
  ps <- getProbs
  return (Map.lookup x ps)

deleteProb :: GName -> TCM ()
deleteProb x = do
  ps <- getProbs
  setProbs (Map.delete x ps)

insertProb :: GName -> Prob -> TCM ()
insertProb x p = do
  ps <- getProbs
  setProbs (Map.insert x p ps)

updateProb :: GName -> (Prob -> TCM MProb) -> TCM ()
updateProb x f = lookupProb x >>= \case
  Nothing -> return ()
  Just p -> f p >>= \case
    Nothing -> deleteProb x
    Just p' -> insertProb x p'

probGNames :: TCM [GName]
probGNames = Map.keys <$> getProbs

unsolvedProbs :: TCM [Prob]
unsolvedProbs = nub <$> Map.elems <$> getProbs

----------------------------------------------------------------------
