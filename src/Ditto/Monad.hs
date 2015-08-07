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
  }

initialR :: DittoR
initialR = DittoR
  { ctx = []
  }

extCtx :: Name -> Exp -> DittoR -> DittoR
extCtx x _A r = r { ctx = (x , _A) : ctx r }

----------------------------------------------------------------------

data Normality = BetaDelta | Rho
data Lookup = LDef | LType

envName :: Sigma -> Name
envName (Def x _ _) = x
envName (Virt x _ _) = x
envName (DForm x _) = x
envName (DCon x _ _ _) = x

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
  return $ envDef n =<< find (\d -> x == envName d) sig

lookupType :: Name -> TCM (Maybe Exp)
lookupType x = do
  DittoS {sig = sig} <- get
  return $ return . envType =<< find (\d -> x == envName d) sig

lookupCtx :: Name -> TCM (Maybe Exp)
lookupCtx x = do
  DittoR {ctx = ctx} <- ask
  maybe (return $ lookup x ctx) (return . Just) =<< lookupType x

----------------------------------------------------------------------

