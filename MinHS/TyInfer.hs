module MinHS.TyInfer where

import MinHS.Bwd
import MinHS.Syntax
import qualified MinHS.Subst as S (Subst, SubstSem, substFlex, substRigid, fromList)
import MinHS.TCMonad
import Debug.Trace

import Control.Monad (foldM)
import Data.List (delete)
import Data.Set (Set, notMember, fromList, difference, member, toList)
import Data.Bifunctor (Bifunctor(..), second)
import MinHS.Subst ((=:))

-- | A monomorphic type injected into a type scheme with no quantified
-- type variables.
mono :: Type -> Scheme
mono t = Forall [] t

primOpType :: Op -> Scheme
primOpType Gt   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = mono $ Base Int `Arrow` Base Int
primOpType Fst  = Forall ["a","b"] $ (RigidVar "a" `Prod` RigidVar "b") `Arrow` RigidVar "a"
primOpType Snd  = Forall ["a","b"] $ (RigidVar "a" `Prod` RigidVar "b") `Arrow` RigidVar "b"
primOpType _    = mono $ Base Int `Arrow` (Base Int `Arrow` Base Int)

conType :: Id -> Maybe Scheme
conType "True"  = Just $ mono $ Base Bool
conType "False" = Just $ mono $ Base Bool
conType "()"    = Just $ mono $ Base Unit
conType "Pair"  = Just
                  $ Forall ["a","b"]
                  $ RigidVar "a" `Arrow` (RigidVar "b" `Arrow` (RigidVar "a" `Prod` RigidVar "b"))
conType "Inl"   = Just
                  $ Forall ["a","b"]
                  $ RigidVar "a" `Arrow` (RigidVar "a" `Sum` RigidVar "b")
conType "Inr"   = Just
                  $ Forall ["a","b"]
                  $ RigidVar "b" `Arrow` (RigidVar "a" `Sum` RigidVar "b")
conType _       = Nothing

freshForall :: [Id] -> TC [(Id,Id)]
freshForall xs = mapM (\x -> (,) <$> pure x <*> freshId) xs

-- | Produce fresh flexible variables for a type scheme
specialise :: Scheme -> TC (Type, Suffix)
specialise (Forall xs t) =
  do ids <- freshForall xs
     return (S.substRigid (S.fromList (map (second FlexVar) ids)) t
            , map (flip (,) HOLE . snd) ids)

-- | Extend a typing context with a collection of flexible declarations
extend :: Gamma -> Suffix -> Gamma
extend g [] = g
extend g ((v,d) : ds) = extend (g :< v := d) ds

infer :: Program -> Either TypeError (Program, Gamma)
infer program = runTC $ inferProgram BEmpty program

-- Get scheme corresponding to a variable starting from the most local vars.
varScheme :: Gamma -> Id -> Maybe Scheme
varScheme BEmpty _ = Nothing  -- Empty context or no matching entry
varScheme (g :< entry) x =
  case entry of
    TermVar entryId scheme | entryId == x -> Just scheme
    _ -> varScheme g x


-- | Perform unification of the given types
unify :: Gamma -> Type -> Type -> TC Gamma
-- skip-mark
unify (g :< Mark) (FlexVar t1) (FlexVar t2) = 
  do
    g2 <- unify g (FlexVar t1) (FlexVar t2)
    return (g2 :< Mark)
-- skip-term
unify (g :< (TermVar x s)) (FlexVar t1) (FlexVar t2) =
  do
    g2 <- unify g (FlexVar t1) (FlexVar t2)
    return (g2 :< (TermVar x s))
unify (g :< (p := HOLE)) (FlexVar t1) (FlexVar t2) =
  -- skip-type
  if p /= t1 && p /= t2 then
    do 
      g2 <- unify g (FlexVar t1) (FlexVar t2)
      return (g2 :< p := HOLE)
  -- defn
  else
    if (p == t1 && t1 /= t2) then
      return (g :< (t1 := (Defn (FlexVar t2))))
    else 
      if t1 == t2 then return g
      else do_unify g (FlexVar t1) (FlexVar t2)

-- reflexivity
unify g t1 t2 = 
  if t1 == t2 then 
    return g
  else do_unify g t1 t2

do_unify :: Gamma -> Type -> Type -> TC Gamma
do_unify g (Arrow t1 t2) (Arrow t1' t2') = 
  do
    g2 <- unify g t1 t1'
    g3 <- unify g2 t2 t2'
    return g3  
do_unify g (Prod t1 t2) (Prod t1' t2') = 
  do
    g2 <- unify g t1 t1'
    g3 <- unify g2 t2 t2'
    return g3  
do_unify g (Sum t1 t2) (Sum t1' t2') = 
  do
    g2 <- unify g t1 t1'
    g3 <- unify g2 t2 t2'
    return g3
-- subst
do_unify (g :< (p := Defn a)) t1 t2 = 
  do
    g2 <- unify g (S.substFlex (p =: a) t1) (S.substFlex (p =: a) t2)
    return (g2 :< (p := Defn a))
-- inst
do_unify g (FlexVar t1) (FlexVar t2) = typeError (UnifyFailed g (FlexVar t1) (FlexVar t2))
do_unify g (FlexVar t1) t2 = inst g [] t1 t2
do_unify g t1 (FlexVar t2) = inst g [] t2 t1
do_unify g t1 t2 = typeError (UnifyFailed g t1 t2)


-- | Instantiation the type variable a with the type t
inst :: Gamma -> Suffix -> Id -> Type -> TC Gamma
-- skip-mark
inst (g :< Mark) zs a t = 
  do
    g2 <- (inst g zs a t)
    return (g2 :< Mark)
-- skip-term
inst (g :< (TermVar x s)) zs a t =
  do
    g2 <- (inst g zs a t)
    return (g2 :< (TermVar x s))
-- subst
inst (g :< (b := Defn t')) zs a t =
  do 
    g2 <- unify (extend g zs) (S.substFlex (b =: t') (FlexVar a)) (S.substFlex (b =: t') t)
    return (g2 :< (b := Defn t'))
inst (g :< (b := HOLE)) zs a t =
  -- defn
  if b == a then
    if not (member a (ffv t)) then
      return ((extend g zs) :< (a := Defn t))
    else
      typeError (OccursCheckFailed (g :< (b := HOLE)) a t)
  else
    -- depend
    if member b (ffv t) then 
        inst g ((b, HOLE) : zs) a t
    -- skip-type
    else
      do 
        g2 <- inst g zs a t
        return (g2 :< (b := HOLE))
inst g zs a t = error "implement me!"


inferProgram :: Gamma -> Program -> TC (Program, Gamma)
inferProgram g (SBind x _ e) = 
  do 
    (t, g') <- (generalise g e [])
    return (SBind x (Just t) e, g')



inferExp :: Gamma -> Exp -> TC (Type, Gamma)
inferExp g (Num _) = return (Base Int, g)
inferExp g (Con x) = 
  maybe (typeError (NoSuchConstructor x)) specialise (conType x) >>= \(ty, suffix) -> return (ty, extend g suffix)
inferExp g (Prim op) = specialise (primOpType(op)) >>= \(ty, suffix) -> return (ty, extend g suffix)
inferExp g (Var x) = 
  maybe (typeError (NoSuchVariable x)) specialise (varScheme g x) >>= \(ty, suffix) -> return (ty, extend g suffix)
inferExp g1 (App e1 e2) =
  do
    (t1, g2) <- inferExp g1 e1
    (t2, g3) <- inferExp g2 e2
    a <- freshId
    g4 <- unify (g3 :< (a := HOLE)) t1 (Arrow t2 (FlexVar a))
    -- z <- error (show g4)
    return ((FlexVar a), g4)
inferExp g1 (If e et ef) = 
  do
    (t, g2) <- inferExp g1 e
    g3 <- unify g2 t (Base Bool)
    (tt, g4) <- inferExp g3 et
    (tf, g5) <- inferExp g4 ef
    g6 <- unify g5 tt tf
    return (tt, g6)
inferExp g (Case e _) = typeError MalformedAlternatives
inferExp _ _ = typeError MalformedAlternatives

-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives


generalise :: Gamma -> Exp -> [Id] -> TC (Scheme, Gamma)
generalise g e v = 
  do
    (t, g') <- inferExp (g :< Mark) e
    let s = takeWhilst (\c ->
          case c of
            Mark -> False
            _    -> True) g' in return ((gen s t v), g')
generalise _ _ _ = error ""

gen :: Gamma -> Type -> [Id] -> Scheme
gen (x :< Mark) y z = (do_gen x y z)
gen x y z = do_gen x y z


do_gen :: Gamma -> Type -> [Id] -> Scheme
do_gen (s :< (x := HOLE)) t v = do_gen s (S.substFlex (x =: (fix [x] (FlexVar x))) t) (x : v)
do_gen (s :< (x := Defn b)) t v = do_gen s (S.substFlex (x =: b) t) v
do_gen BEmpty t v = Forall v t
do_gen _ _ _ = error "Unexpected Symbol in Context"