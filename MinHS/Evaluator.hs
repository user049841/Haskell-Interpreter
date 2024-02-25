module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Prettyprinter as PP

type VEnv = E.Env Value

data Value = I Integer
           | F VEnv Id Exp
           | P Op [Value]
           | C Id [Value]
           deriving (Show)

instance {-# OVERLAPPING #-} ANSIPretty Value where
  ansipp (I i) = numeric $ i
  ansipp (P o []) | o `elem` [Fst , Snd ] = ansipp o
                  | otherwise             = PP.parens $ ansipp o
  ansipp (P Fst vs) = PP.parens (primop "fst" PP.<+> ansippList vs)
  ansipp (P Snd vs) = PP.parens (primop "snd" PP.<+> PP.hsep (map ansipp vs))
  ansipp (P o vs) = PP.parens (PP.parens (ansipp o) PP.<+> ansippList vs)
  ansipp (C c []) = datacon c
  ansipp (C c vs) = PP.parens (datacon c PP.<+> ansippList vs)
  ansipp (F _ x e) = red (PP.pretty "<<") PP.<> PP.pretty x PP.<> PP.pretty "."
                             PP.<+> ansipp e PP.<+> red (PP.pretty ">>")

evaluate :: Program -> Value
evaluate (SBind _ _ e) = evalE E.empty e

evalMBind :: VEnv -> MBind -> Value
evalMBind g (MBind _ x e) = evalF (F g x e)

evalSBind :: VEnv -> SBind -> Value
evalSBind g (SBind _ _ e) = evalE g e

boundName :: SBind -> Id
boundName (SBind f _  _) = f

evalF :: Value -> Value
evalF (F e [] x) = evalE e x
evalF x          = x

evalE :: VEnv -> Exp -> Value
evalE g (Var x) = case E.lookup g x of
  Just v -> v
  Nothing -> error $ "invariant broken: no variable " ++ x ++ " bound"
evalE _ (Num i)        = I i
evalE _ (Con x)        = C x []
evalE _ (Prim o)       = P o []
evalE g (If c t f)     =
  case evalE g c of
    C "True"  [] -> evalE g t
    C "False" [] -> evalE g f
    _            -> error "invariant broken: boolean value expected"
evalE g (Let (b:bs) e) = evalE (g `E.add` (boundName b, evalSBind g b)) (Let bs e)
evalE g (Let [] e)     = evalE g e
evalE g (Case e cs)  = tryAlts (evalE g e) cs
   where tryAlts (C c as) (Alt t ps y :_) | c == t = evalE (E.addAll g (zip ps as)) y
         tryAlts v (_:xs) = tryAlts v xs
         tryAlts _ [] = error "Pattern match failure"

evalE g (Recfun b@(MBind f _ _))     = let v = evalMBind (g `E.add` (f, v)) b
                          in v
evalE g (App a b) =
  case evalE g a of
    P o v    -> evalOp o (v ++ [evalE g b])
    C c v    -> C c (v ++ [evalE g b])
    (F g' x e) -> evalE (g' `E.add` (x, evalE g b)) e
    _        -> error "invariant broken: operator type cannot be applied"

evalOp :: Op -> [Value] -> Value
evalOp Neg  [I x    ] = I $ (-x)
evalOp Add  [I x,I y] = I $ x + y
evalOp Sub  [I x,I y] = I $ x - y
evalOp Mul  [I x,I y] = I $ x * y
evalOp Quot [I x,I 0] = error "divide by zero"
evalOp Rem  [I x,I 0] = error "divide by zero"
evalOp Quot [I x,I y] = I $ x `div` y
evalOp Rem  [I x,I y] = I $ x `rem` y
evalOp Gt   [I x,I y] = flip C [] . show $ x >  y
evalOp Ge   [I x,I y] = flip C [] . show $ x >= y
evalOp Lt   [I x,I y] = flip C [] . show $ x <  y
evalOp Le   [I x,I y] = flip C [] . show $ x <= y
evalOp Eq   [I x,I y] = flip C [] . show $ x == y
evalOp Ne   [I x,I y] = flip C [] . show $ x /= y
evalOp Fst  [C "Pair" [a,b]] = a
evalOp Snd  [C "Pair" [a,b]] = b
evalOp s x = P s x
