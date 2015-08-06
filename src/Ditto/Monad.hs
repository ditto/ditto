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
  }

type TCM = StateT DittoS (ReaderT DittoR (ExceptT String Identity))

lookupDef :: Name -> TCM (Maybe Exp)
lookupDef = error "lookup not implemented"