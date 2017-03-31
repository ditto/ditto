module Ditto.Expand
  ( expand
  , expands
  , expandBind
  , deltaForm
  , metaForm
  ) where
import Ditto.Syntax
import Ditto.Monad
import Ditto.Sub

----------------------------------------------------------------------

type Form = [Expansion]
data Expansion = XDelta | XBeta | XMeta | XGuard
  deriving (Show, Read, Eq)

deltaForm = [XDelta, XBeta, XMeta, XGuard]
metaForm = [XBeta, XMeta, XGuard]

----------------------------------------------------------------------

expand :: Form -> Exp -> TCM Exp
expand form EType = return EType
expand form (EInfer m) = EInfer <$> return m
expand form (EPi i _A _B) = EPi i <$> expand form _A <*> expandBind form i _A _B
expand form (ELam i _A b) = ELam i <$> expand form _A <*> expandBind form i _A b
expand form (EApp i f a) = expand form f >>= \case
  ELam _ _ bnd_b | elem XBeta form -> do
    (x, b) <- unbind bnd_b
    expand form =<< sub1 (x , a) b
  f -> EApp i f <$> expand form a
expand form (EForm x as) = EForm x <$> expands form as
expand form (ECon x as) = ECon x <$> expands form as
expand form (ERed x as) = ERed x <$> expands form as
expand form (EMeta x as) = eleM XMeta form (lookupMeta x) >>= \case
  Just a -> expand form (apps a as)
  Nothing -> EMeta x <$> expands form as
expand form (EGuard x) = eleM XGuard form (lookupGuard x) >>= \case
  Just a -> expand form a
  Nothing -> return (EGuard x)
expand form (EVar x) = eleM XDelta form (lookupDef x) >>= \case
  Just a -> expand form a
  Nothing -> return (EVar x)

expands :: Form -> Args -> TCM Args
expands form = mapM (\(i, a) -> (i,) <$> expand form a)

expandBind :: Form -> Icit -> Exp -> Bind -> TCM Bind
expandBind form i _A bnd_b = do
  (x, b) <- unbind bnd_b
  Bind x <$> expand form b

eleM :: Expansion -> Form -> TCM (Maybe Exp) -> TCM (Maybe Exp)
eleM x xs m = if elem x xs then m else return Nothing

----------------------------------------------------------------------
