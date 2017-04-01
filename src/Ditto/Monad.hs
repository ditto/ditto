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
  , defs :: Defs
  , metas :: Metas
  , sols :: Sols
  , guards :: Guards
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
  , defs = Map.empty
  , metas = Map.empty
  , sols = Map.empty
  , guards = Map.empty
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

lookupCon :: PName -> TCM (Maybe Con)
lookupCon x = do
  env <- getEnv
  return $ conSig x =<< find (isPNamed x) env

lookupCons :: PName -> TCM (Maybe Cons)
lookupCons x = do
  env <- getEnv
  return $ conSigs =<< find (isPNamed x) env

lookupRedType :: PName -> TCM (Maybe (Tel, Exp))
lookupRedType x = do
  env <- getEnv
  return $ redType =<< find (isPNamed x) env

lookupRedClauses :: PName -> TCM (Maybe Clauses)
lookupRedClauses x = do
  env <- getEnv
  return $ redClauses =<< find (isPNamed x) env

lookupRedDelta :: PName -> TCM (Maybe Exp)
lookupRedDelta x = lookupRedClauses x >>= \case
  Just [([], [], MapsTo a)] -> return (Just a)
  _ -> return Nothing

----------------------------------------------------------------------

getMetas :: TCM Metas
getMetas = metas <$> get

undefMetas :: (MName -> Bool) -> TCM Holes
undefMetas f = do
  xs <- (\\) <$> (Map.keys <$> getMetas) <*> (Map.keys <$> getSols)
  mapM (\x -> (x,) <$> lookupMeta x) (filter f xs)

unsolvedMetas :: TCM Holes
unsolvedMetas = undefMetas (not . isHole)

holeMetas :: TCM Holes
holeMetas = undefMetas isHole

lookupMeta :: MName -> TCM Meta
lookupMeta x = fromJust . Map.lookup x <$> getMetas

insertMeta :: MName -> Acts -> Tel -> Exp -> TCM ()
insertMeta x acts ctx _A = do
  state@DittoS { metas = metas } <- get
  put state { metas = Map.insert x (Meta acts ctx _A) metas }

----------------------------------------------------------------------

getSols :: TCM Sols
getSols = sols <$> get

lookupSol :: MName -> TCM (Maybe Exp)
lookupSol x = Map.lookup x <$> getSols

insertSol :: MName -> Exp -> TCM ()
insertSol x a = do
  state@DittoS { sols = sols } <- get
  put state { sols = Map.insert x a sols }

----------------------------------------------------------------------

getGuards :: TCM Guards
getGuards = guards <$> get

lookupGuard :: GName -> TCM (Maybe Exp)
lookupGuard x = lookupProb x >>= \case
  Just _ -> return Nothing
  Nothing -> liftM val . Map.lookup x <$> getGuards

lookupGuardType :: GName -> TCM (Maybe Exp)
lookupGuardType x = liftM typ . Map.lookup x <$> getGuards

insertGuard :: GName -> Exp -> Exp -> TCM ()
insertGuard x a _A = do
  state@DittoS { guards = guards } <- get
  put state { guards = Map.insert x (Ann a _A) guards }

----------------------------------------------------------------------

lookupPSigma :: PName -> TCM (Maybe Sigma)
lookupPSigma x = do
  env <- getEnv
  return $ return =<< find (isPNamed x) env

----------------------------------------------------------------------

getDefs :: TCM Defs
getDefs = defs <$> get

allDefs :: TCM [(Name, Ann)]
allDefs = Map.assocs <$> getDefs

allNames :: TCM [Name]
allNames = Map.keys <$> getDefs

lookupDef :: Name -> TCM (Maybe Exp)
lookupDef x = liftM val . Map.lookup x <$> getDefs

lookupType :: Name -> TCM (Maybe Exp)
lookupType x = lookupCtx x >>= \case
  Just _A -> return (Just _A)
  Nothing -> liftM typ . Map.lookup x <$> getDefs

insertDef :: Name -> Exp -> Exp -> TCM ()
insertDef x a _A = do
  state@DittoS { defs = defs } <- get
  put state { defs = Map.insert x (Ann a _A) defs }

----------------------------------------------------------------------

lookupCtx :: Name -> TCM (Maybe Exp)
lookupCtx x = do
  ctx <- getCtx
  return $ lookupTel x ctx

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
