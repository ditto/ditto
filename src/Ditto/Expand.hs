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
expand form Type = return Type
expand form TYPE = return TYPE
expand form (Infer m) = Infer <$> return m
expand form (Pi i _A _B) = Pi i <$> expand form _A <*> expandBind form i _A _B
expand form (Lam i _A b) = Lam i <$> expand form _A <*> expandBind form i _A b
expand form (App i f a) = expand form f >>= \case
  Lam _ _ bnd_b | elem XBeta form -> do
    (x, b) <- unbind bnd_b
    expand form =<< sub1 (x , a) b
  f -> App i f <$> expand form a
expand form (Form x as) = Form x <$> expands form as
expand form (Con x as) = Con x <$> expands form as
expand form (Red x as) = Red x <$> expands form as
expand form (Meta x as) = eleM XMeta form (lookupMeta x) >>= \case
  Just a -> expand form (apps a as)
  Nothing -> Meta x <$> expands form as
expand form (Guard x) = eleM XGuard form (lookupGuard x) >>= \case
  Just a -> expand form a
  Nothing -> return (Guard x)
expand form (Var x) = eleM XDelta form (lookupDef x) >>= \case
  Just a -> expand form a
  Nothing -> return (Var x)

expands :: Form -> Args -> TCM Args
expands form = mapM (\(i, a) -> (i,) <$> expand form a)

expandBind :: Form -> Icit -> Exp -> Bind -> TCM Bind
expandBind form i _A bnd_b = do
  (x, b) <- unbind bnd_b
  Bind x <$> expand form b

eleM :: Expansion -> Form -> TCM (Maybe Exp) -> TCM (Maybe Exp)
eleM x xs m = if elem x xs then m else return Nothing

----------------------------------------------------------------------
