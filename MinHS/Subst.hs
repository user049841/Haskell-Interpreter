module MinHS.Subst ( Subst
                   , SubstSem
                   , substFlex
                   , substRigid
                   , fromList
                   , (=:)
                   ) where

import MinHS.Syntax
newtype Subst = Subst [(Id, Type)]

instance Semigroup Subst where
  Subst a <> Subst b = Subst $ a ++ b

instance Monoid Subst where
  mempty = Subst []
  mappend = (<>)

class SubstSem a where
  -- | Perform substitution on rigid type variables.
  substRigid :: Subst -> a -> a
  -- | Perform substitution on flexible type variables.
  substFlex  :: Subst -> a -> a

-- | A substitution semantics for types.
instance SubstSem Type where
  -- | Used for specialisation
  substRigid s (Sum a b)   = Sum (substRigid s a) (substRigid s b)
  substRigid s (Prod a b)  = Prod (substRigid s a) (substRigid s b)
  substRigid s (Arrow a b) = Arrow (substRigid s a) (substRigid s b)
  substRigid (Subst s) (RigidVar x) | Just t <- lookup x s = substRigid (Subst s) t
                                  | otherwise            = RigidVar x
  substRigid _         t   = t

  -- | Used for unification.
  substFlex s (Sum a b)   = Sum (substFlex s a) (substFlex s b)
  substFlex s (Prod a b)  = Prod (substFlex s a) (substFlex s b)
  substFlex s (Arrow a b) = Arrow (substFlex s a) (substFlex s b)
  substFlex (Subst s) (FlexVar x) | Just t <- lookup x s = substFlex (Subst s) t
                                | otherwise            = FlexVar x
  substFlex _         t   = t

-- | A substitution semantics for expressions
instance SubstSem Exp where
  substRigid _ e = e
  -- substRigid _ e@(Var _) = e
  -- substRigid _ e@(Prim _) = e
  -- substRigid _ e@(Con _) = e
  -- substRigid _ e@(Num _) = e
  -- substRigid s (App e1 e2) = App (substRigid e1) (substRigid e2)
  substFlex _ e = e

(=:) :: Id -> Type -> Subst
x =: t = Subst [(x,t)]

fromList :: [(Id,Type)] -> Subst
fromList = Subst
