module Ditto.Check where
import Ditto.Syntax

-- import Control.Monad.State

data DittoS = DittoS
  { datas :: [DataDecl]
  }

data DittoR = DittoR
  { ctx :: Tel
  }


-- type TCM = StateT SpireS (ReaderT SpireR (ExceptT String FreshM))

-- infer
