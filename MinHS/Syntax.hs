module MinHS.Syntax where
import Data.Set

type Id = String

type Program = SBind

data Exp
    = Var Id
    | Prim Op
    | Con Id
    | Num Integer
    | App Exp Exp
    | If Exp Exp Exp
    | Let [SBind] Exp
    | Recfun MBind
    | Case Exp [Alt]
    deriving (Read,Show,Eq)

data Alt = Alt Id [Id] Exp
    deriving (Read,Show,Eq)

data MBind = MBind Id Id Exp
  deriving (Read,Show,Eq)

data SBind = SBind Id (Maybe Scheme) Exp
  deriving (Read,Show,Eq)

data Op = Add
        | Sub
        | Mul
        | Quot
        | Rem
        | Neg
        | Gt
        | Ge
        | Lt
        | Le
        | Eq
        | Ne
        | Fst
        | Snd
        deriving (Show, Eq, Read)

data Scheme = Forall [Id] Type
           deriving (Read, Show, Eq, Ord)

data Type = Arrow Type Type
          | Prod Type Type
          | Sum Type Type
          | Base BaseType
          | FlexVar Id
          | RigidVar Id
          deriving (Read, Show, Eq, Ord)

-- | Shorter constructor for flexible variables.
flex :: Id -> Type
flex = FlexVar

-- | The set of free rigid type variables in a type, assuming they are
-- not bound by some outer forall quantifier.
frv :: Type -> Set Id
frv (Arrow t1 t2) = frv t1 `union` frv t2
frv (Prod t1 t2) = frv t1 `union` frv t2
frv (Sum t1 t2) = frv t1 `union` frv t2
frv (FlexVar _) = empty
frv (RigidVar x) = singleton x
frv (Base _) = empty

-- | The set of free flexible variables in a type.
ffv :: Type -> Set Id
ffv (Arrow t1 t2) = ffv t1 `union` ffv t2
ffv (Prod t1 t2) = ffv t1 `union` ffv t2
ffv (Sum t1 t2) = ffv t1 `union` ffv t2
ffv (FlexVar x) = singleton x
ffv (RigidVar _) = empty
ffv (Base _) = empty

-- | Turn all the flexible variables given into rigid type variables
-- (for generalisation).
fix :: [Id] -> Type -> Type
fix ids (a `Arrow` b) = fix ids a `Arrow` fix ids b
fix ids (Prod a b) = Prod (fix ids a) (fix ids b)
fix ids (Sum  a b) = Sum (fix ids a) (fix ids b)
fix ids (FlexVar x) | x `elem` ids = RigidVar x
                    | otherwise = FlexVar x
fix _ t = t

data BaseType = Unit
              | Bool
              | Int
              deriving (Read, Show, Eq, Ord)

binApply :: Exp -> Exp -> Exp -> Exp
binApply e1 e2 e3 = App (App e1 e2) e3
