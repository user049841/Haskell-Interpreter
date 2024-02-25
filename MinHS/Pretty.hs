{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
module MinHS.Pretty where
import MinHS.Syntax
import MinHS.TCMonad

import Prettyprinter as PP
import Prettyprinter.Render.Terminal

primop :: String -> Doc AnsiStyle
primop = annotate (colorDull Yellow) . pretty

blue = annotate (color Blue)
red = annotate (color Red)
keyword = annotate bold . pretty
datacon = annotate (colorDull Green) . pretty
typecon = annotate (color Blue) . pretty
numeric = annotate (colorDull Cyan) . pretty
symbol = annotate (color Magenta) . pretty
flexvar = annotate (color Yellow) . pretty
rigidvar = annotate (color White) . pretty
err = annotate (color Red) . pretty

-- Helper typeclass to for specialising to an AnsiStyle annotation.
class ANSIPretty a where
  ansipp :: a -> Doc AnsiStyle

  ansippList :: [a] -> Doc AnsiStyle
  ansippList = align . list . map ansipp

instance Pretty a => ANSIPretty a where
  ansipp = pretty

instance {-# OVERLAPPING #-} ANSIPretty MBind where
  ansipp (MBind f ps e) = pretty f <+> params (symbol "=" <+> ansipp e)
      where params = if null ps then id else (hsep (map pretty ps) <+>)
  ansippList = vcat . map (<> semi) . map ansipp

instance Pretty MBind where
  pretty = unAnnotate . ansipp

instance {-# OVERLAPPING #-} ANSIPretty SBind where
  ansipp (SBind f (Just ty) e) =
    pretty f <+> symbol "::" <+> ansipp ty <+> symbol "=" <+> ansipp e
  ansipp (SBind f Nothing e) = pretty f <+> symbol "=" <+> ansipp e
  ansippList = vcat . map (<> semi) . map ansipp

instance Pretty SBind where
  pretty = unAnnotate . ansipp

instance {-# OVERLAPPING #-} ANSIPretty Scheme where
  ansipp = ansippScheme

ansippScheme :: Scheme -> Doc AnsiStyle
ansippScheme (Forall xs t) = tvars (ansipp t)
  where
    tvars p = if null xs then p
      else (keyword "forall" <+>
            hsep (map pretty xs) <> symbol "." <+> p)


instance {-# OVERLAPPING #-} ANSIPretty Type where
  ansipp = prettyType
    where
      prettyType (a `Arrow` b) = prettyType a <+> symbol "->" <+> prettyType b
      prettyType (Sum a b)     = prettyType' a <+> typecon "+" <+> prettyType' b
      prettyType (Prod a b)    = prettyType' a <+> typecon "*" <+> prettyType' b
      prettyType (FlexVar x)   = flexvar $ "f$" ++ tail x
      prettyType (RigidVar x)  = rigidvar x
      prettyType (Base b)      = ansipp b

      prettyType' t@(a `Arrow` b) = parens (prettyType t)
      prettyType' t@(Sum a b)     = parens (prettyType t)
      prettyType' t@(Prod a b)     = parens (prettyType t)
      prettyType' t = prettyType t


instance {-# OVERLAPPING #-} ANSIPretty BaseType where
  ansipp Unit = typecon "()"
  ansipp Bool = typecon "Bool"
  ansipp Int  = typecon "Int"

instance {-# OVERLAPPING #-} ANSIPretty Op where
  ansipp Add  = pretty "+"
  ansipp Sub  = pretty "-"
  ansipp Mul  = pretty "*"
  ansipp Quot = pretty "/"
  ansipp Rem  = pretty "%"
  ansipp Neg  = pretty "negate"
  ansipp Gt   = pretty ">"
  ansipp Ge   = pretty ">="
  ansipp Lt   = pretty "<"
  ansipp Le   = pretty "<="
  ansipp Eq   = pretty "=="
  ansipp Ne   = pretty "/="
  ansipp Fst  = pretty "fst"
  ansipp Snd  = pretty "snd"

instance {-# OVERLAPPING #-} ANSIPretty Exp where
  ansipp (Var i) = pretty i
  ansipp (App (App (Con "Pair") e1) e2) = parens $ ansipp e1 <> comma <+> ansipp e2
  ansipp (App (Prim Neg) e2) = parens (pretty "-" <+> ansipp' e2)
  ansipp (Prim Fst) = pretty "fst"
  ansipp (Prim Snd) = pretty "snd"
  ansipp (Prim o) = parens (ansipp o)
  ansipp (Con i) = datacon i
  ansipp (Num i) = numeric i
  ansipp (App e1 e2) = ansipp e1 <+> ansipp' e2
  ansipp (If c t e) = keyword "if"
                      <+> align (PP.vsep [ansipp c
                                         , keyword "then" <+> ansipp t
                                         , keyword "else" <+> ansipp e])
  ansipp (Let bs e)  =
    align (PP.vsep [ keyword "let" <+> align (encloseSep mempty semi mempty $ map ansipp bs)
                   , keyword "in" <+> ansipp e])
  ansipp (Recfun b)  = parens (keyword "recfun" <+> ansipp b)
  ansipp (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) =
    keyword "case" <+> ansipp e <+> keyword "of" <+>
    braces (pretty "Inl" <+> pretty x <+> symbol "->" <+> ansipp e1 <> semi <+>
            pretty "Inr" <+> pretty y <+> symbol "->" <+> ansipp e2 <> semi)
  ansipp (Case _ _) = pretty "CASE"

ansipp' :: Exp -> Doc AnsiStyle
ansipp' t@(App (App (Con "Pair") _) _) = ansipp t
ansipp' t@(App _ _) = parens (ansipp t)
ansipp' t           = ansipp t

instance {-# OVERLAPPING #-} ANSIPretty TypeError where
   ansipp (TypeMismatch t1 t2 e) = PP.vsep [ err "Type mismatch:"
                                           , indent 3 (ansipp t1)
                                           , err "is not"
                                           , indent 3 (ansipp t2)
                                           , err "in expression"
                                           , indent 3 (ansipp e)]
   ansipp (TypeShouldBeFunction ty b) =
     PP.vsep [ err "Parameter list suggests this atomic type"
             , indent 3 (ansipp ty)
             , err "to be a function, in binding:"
             , indent 3 (ansipp b)]
   ansipp (FunctionTypeExpected e t) =
     PP.vsep [err "Function application must be performed on a function, but this:"
             , indent 3 (ansipp e)
             , err "is of type" <+> ansipp t]
   ansipp (NoSuchVariable x) =  err "Variable"
                            <+> pretty x
                            <+> err "not in scope."
   ansipp (NoSuchConstructor x) =  err "Constructor"
                               <+> pretty x
                               <+> err "not in scope."
   ansipp (TypeConstructorSaturated t k) =  err "Expected"
                                        <+> ansipp t
                                        <+> err "to be a type constructor, but it is an atomic type."
   ansipp (KindMismatch k1 k2 t) =  err "Type term"
                                <+> ansipp t
                                <+> err "is not valid."
   ansipp MissingType = err "missing type"
   ansipp (OccursCheckFailed g x t) =
     err "occurs check failure for " <+> ansipp x <+> err " at type " <+> ansipp t <+>
     err ("in context " ++ show g)
   ansipp MalformedAlternatives = err "malformed alternatives"
   ansipp ForallInRecfun = err "recfun should be monomorphic"
   ansipp (UnifyFailed g t1 t2) = err "failed to unify "
                                <+> ansipp t1 <+> err " with " <+> ansipp t2 <+>
                                err ("in context " ++ show g)
   ansipp (InstFailed zs a t) = err "failed to instantiate " <+> ansipp a
                               <+> err " with " <+> ansipp t <+>
                               err ("with suffix " ++ show zs)
   ansipp (Diagnostic s) = err s
