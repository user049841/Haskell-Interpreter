module MinHS.TCMonad where

import MinHS.Syntax
import Control.Monad
import MinHS.Bwd ( Bwd )

-- | Our typing contexts are backward lists of entries.
type Gamma = Bwd Entry

-- | An entry is either a term variable, a flexible variable
-- declaration, or a marker.
data Entry = TermVar Id Scheme
           | (:=) Id Decl
           | Mark
           deriving (Read,Show)

instance Eq Entry where
  TermVar x _ == TermVar y _ = x == y
  a := _      == b := _      = a == b
  Mark        == Mark        = True
  _           == _           = False

-- | A declaration is either an uninstantiated hole, or a type
-- assignment.
data Decl = HOLE | Defn Type
          deriving (Read,Show,Eq)

-- | A suffix is a list of flexible declarations.
type Suffix = [(Id, Decl)]

data TypeError = TypeMismatch Type Type Exp
               | TypeShouldBeFunction Type MBind
               | FunctionTypeExpected Exp Type
               | NoSuchVariable Id
               | NoSuchConstructor Id
               | TypeConstructorSaturated Type Kind
               | KindMismatch Kind Kind Type
               | MissingType
               -- | TCMonad errors
               | OccursCheckFailed Gamma Id Type
               | MalformedAlternatives
               | ForallInRecfun -- REMOVE?: I've prevented this with MBind vs. SBind
               | UnifyFailed Gamma Type Type
               | InstFailed Suffix Id Type
               | Diagnostic String
               deriving (Show)

data Kind = Star
          | (:=>) Kind Kind
          deriving (Show, Eq)

newtype TC a = TC ([Id] -> Either TypeError ([Id], a))

instance Applicative TC where
  pure x = TC (\s -> Right (s,x))
  (<*>) = ap

instance Functor TC where
  fmap = ap . pure

instance Monad TC where
  return = pure
  (TC f) >>= k = TC (\ns -> case f ns of
                             Left terr -> Left terr
                             Right (ns', x) ->
                               let TC g = k x in g ns')

freshNames :: [Id]
freshNames = let as = map ((++) "'" . pure) ['a'..'z']
                 ns = map show [1..] in
  concatMap (flip map as . flip (++)) ns

runTC :: TC a -> Either TypeError a
runTC (TC f) = fmap snd (f freshNames)

typeError :: TypeError -> TC a
typeError = TC . const . Left

freshId :: TC Id
freshId = TC $ \(x:xs) -> Right (xs, x)
