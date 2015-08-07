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
  DittoR {rhoExpandable = expand} <- ask
  DittoS {sig = sig} <- get
  return $ lookupDefType x expand LuDef sig


lookupVirt :: Name -> TCM (Maybe Exp)
lookupVirt x = do
  DittoS {sig = sig} <- get
  return $ lookupDefType x True LuDef sig

data LookupK =
    LuDef -- lookup the definition of a name
  | LuTyp -- lookup the type of a name

lookupDefType:: Name -> Bool -> LookupK -> [Sigma] -> Maybe Exp
lookupDefType x virt LuDef ((Def y a _):sig) | x == y  = Just a
lookupDefType x virt LuTyp ((Def y _ a):sig) | x == y  = Just a
lookupDefType x True LuDef ((Virt y a _):sig) | x == y  = Just a
lookupDefType x True LuTyp ((Virt y _ a):sig) | x == y  = Just a
lookupDefType x virt LuTyp ((Data{dname = _, dpars = _, dixs = _, dcons = _}) : sig) =
  error "lookup of datatypes not implemented"
lookupDefType x virt lu (_ : sig) = lookupDefType x virt lu sig
lookupDefType _ _ _ [] = Nothing


lookupType :: Name -> TCM (Maybe Exp)
lookupType x = do
  DittoR {rhoExpandable = expand, ctx = ctx} <- ask
  DittoS {sig = sig} <- get
  case lookupDefType x expand LuTyp sig of
    Just a -> return $ Just a
    Nothing -> return $ lookup x ctx

extCtx :: Name -> Exp -> DittoR -> DittoR
extCtx x _A r = r { ctx = (x , _A) : ctx r }
