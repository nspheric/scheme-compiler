module ToAnf where

import Parser 
    ( Binding(Binding),
      Exp(Application, Let, Prim, If, Varexp, Bool, DefineProc, Lambda, Int, Cons, Nil, Quote, Begin, Set, Cond, FunRef),
      Var(Var),
      Operator(Plus),
      Cnd(Cnd, Else),
      lexer,
      toAst )
import Desugar (desugar)

revealFunctions :: [Exp] -> [Exp]
revealFunctions [] = []
revealFunctions (x:xs) =
  reveal x : revealFunctions xs

reveal :: Exp -> Exp
reveal (Application (Varexp (Var var)) exps) =
  let exps' = map reveal exps in
    Application (FunRef (Var var) (length exps')) exps'

reveal (If cnd thn (Just els)) =
  (If (reveal cnd) (reveal thn) (Just (reveal els)))
reveal (If cnd thn Nothing) =
  (If (reveal cnd) (reveal thn) Nothing)
  
reveal (Prim op e e2) =
  (Prim op (reveal e) (reveal e2))

reveal (DefineProc var vars exp) =
  (DefineProc var vars (reveal exp))

reveal (Lambda vars exp) =
  (Lambda vars (reveal exp))

reveal (Cons e e2) =
  Cons (reveal e) (reveal e2)

reveal x = x

toAnf :: [Exp] -> [Exp]
toAnf [] = []
toAnf (x:xs) =
  toanf x : rest
  where
    rest = toAnf xs
    
toanf :: Exp -> Exp
toanf exp =
  toanf' exp 0


toanf' :: Exp -> Int ->  Exp
toanf' (Prim op e e2) n =
  let tmp = Varexp (Var ("tmp" ++ show n))
      tmp2 = Varexp (Var ("tmp" ++ show (n+1))) in
    if (isatomic e) && (isatomic e2)
    then (Prim op e e2)
    else
      if (isatomic e) && not (isatomic e2) || (isatomic e2) && not (isatomic e)
      then
        if (isatomic e) then makeAnf e2 (Prim op e tmp2) tmp2 (n+1) else  (makeAnf e (Prim op tmp e2) tmp (n+1))
      else
        let e2' = (makeAnf e2 (Prim op tmp tmp2) tmp2  n) in
          (makeAnf e e2' tmp (n + 1))
    
toanf' (If (Bool op) thn (Just els)) n =
  (If (Bool op) (toanf' thn (n+1)) (Just (toanf' els (n+1))))

toanf' (If (Bool op) thn Nothing) n =
  (If (Bool op) (toanf' thn (n+1)) Nothing)

toanf' (If cnd thn (Just els)) n =
  let tmp = ("tmp_" ++ show n) in
    (Let [Binding (Varexp (Var tmp)) (toanf' cnd (n + 1))] (If (Varexp (Var tmp)) (toanf' thn (n + 1)) (Just (toanf' els (n + 1)))))
   
toanf' (If cnd thn Nothing) n =
  let tmp = ("tmp_" ++ show n) in
    (Let [Binding (Varexp (Var tmp)) (toanf' cnd (n + 1))] (If (Varexp (Var tmp)) (toanf' thn (n + 1)) Nothing))
   

toanf' (DefineProc var params exp) n =
  DefineProc var params (toanf' exp n)

toanf' (Lambda vars exp) n =
  (Lambda vars (toanf' exp n))

toanf' (Set v exp) n =
  (Set v (toanf' exp n))
  
toanf' (Cons e e2) n =
  let tmp = Varexp (Var ("tmp" ++ show n))
      tmp2 = Varexp (Var ("tmp" ++ show (n+1))) in
    if (isatomic e) && (isatomic e2)
    then Cons e e2
    else if (isatomic e) && not (isatomic e2) || (isatomic e2) && not (isatomic e) then
    if (isatomic e) then makeAnf e2 (Cons e tmp2) tmp2 (n+1) else makeAnf e (Cons tmp e2) tmp (n+1)
    else
    let e2' = makeAnf e2 (Cons tmp tmp2) tmp2  n in
          makeAnf e e2' tmp (n + 1)
          
toanf' (Application op exps) n =
  let exps' = map (\x -> (toanf' x n)) exps in
    appToAnf (Application op exps') n []

toanf' x n = x
appToAnf (Application (FunRef var n') []) n tmps =
  (Application (FunRef var n')) tmps
    
appToAnf (Application (FunRef var n') (x:xs)) n tmps =
  let tmp = Varexp (Var ("tmp" ++ show n))
      tmp2 = Varexp (Var ("tmp" ++ show n)) in
    case x of
      Int n ->
        let tmps' = x:tmps in
          appToAnf (Application (FunRef var n') xs) (n+1) tmps'
      Varexp (Var v) ->
        let tmps' = x:tmps in
          appToAnf (Application (FunRef var n') xs) (n+1) tmps'
      _->
        let anf' = toanf' x n
            tmps' = tmp:tmps
            app' = appToAnf (Application (FunRef var n') xs) (n+1) tmps' in
          makeAnf x app' tmp (n+1)
          
getIf :: Exp -> Exp
getIf (Let [Binding v e] (If cnd thn els)) =
  (If cnd thn els)

getBind :: Exp -> [Binding]
getBind (Let binding (If cnd thn els)) =
  binding

makeAnf :: Exp -> Exp -> Exp -> Int -> Exp
makeAnf e x y n =
  let anf' = toanf' e n in
    case anf' of
      Let binding body ->
        Let binding (Let [Binding y body] x)
        
      _ ->
        Let [Binding y e] x
                              
isatomic :: Exp -> Bool
isatomic (Int n) = True
isatomic (Varexp (Var n)) = True
isatomic Nil = True
isatomic exp = False
  
getExps :: Exp -> [Exp]
getExps (Application op exps) =
  exps

toanflet :: Exp -> Exp
toanflet (Let [Binding var (Let [Binding var' exp'] body')] body) =
  getApp (Let [Binding var' exp'] body')  var body
toanflet exp = exp
getApp :: Exp -> Exp -> Exp -> Exp
getApp (Application fn exps) var'' body = (Let [Binding var'' (Application fn exps)] body)
getApp (Let [Binding var exp] (Let [Binding var' exp'] body')) var'' body =
  (Let [Binding var exp] (Let [Binding var' exp'] (getApp body' var'' body)))
  
getApp (Let [Binding var exp] (Prim op e e2)) var'' body =
        (Let [Binding var exp] (Let [Binding var'' (Prim op e e2)] body))
        
getDefExp :: Exp -> Exp
getDefExp (DefineProc var vars exp) = exp
