module Ditto.Monad where
import Ditto.Syntax
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.Except

data DittoS = DittoS
  { sig :: [Sigma]
  }

data DittoR = DittoR
  { ctx :: Tel
  , rhoExpandable :: Bool
  }

type TCM = StateT DittoS (ReaderT DittoR (ExceptT String Identity))

initialR :: DittoR
initialR = DittoR
  { ctx = []
  , rhoExpandable = False
  }

lookupDef :: Name -> TCM (Maybe Exp)
lookupDef x = do
  dittoR <- ask
  if rhoExpandable dittoR
  then error "lookup virtual definition not implemented"
  else error "lookup definition not implemented"

lookupType :: Name -> TCM (Maybe Exp)
-- TODO lookup type in sigma or in ctx
lookupType x = error "lookup type not implemented"

extCtx :: Name -> Exp -> DittoR -> DittoR
extCtx x _A r = r { ctx = (x , _A) : ctx r }
