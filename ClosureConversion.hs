module ClosureConversion where

import Parser (
   Exp(Application, Prim, Lambda, DefineProc, If, Set, Varexp, Let, Int, Closure, Tuple, TupleRef, Cond, Begin, Quote),
   Var(Var),
   Operator(Plus),
   Binding(Binding),
   Cnd(Cnd, Else),
   lexer,
   toAst)

import Desugar (desugar)

import ToAnf (toanf, toAnf)
import qualified Data.Map as Map

closure :: [Exp] -> Int -> [Exp]
closure [] n = []
closure (x:xs) n =
  closure' x n ++ closure xs (n+1) 
      
closure' :: Exp -> Int -> [Exp]
closure' (Lambda vars exp)  n  =
  let fvs =  freeVariables vars exp in
    let fn = "fn_" ++ (show n) in
      let arity = length fvs in
        let closr = Closure (Int arity) (Varexp (Var fn)) fvs in
          let fvs' = "fvs_" ++ show n in
            let exp' = (head (closure' exp n)) in
              [makeLets exp' fvs (Var fvs') 0, closr]
              
closure' (If cnd thn els) n =
  let cnd' =  (closure' cnd n) in
    let thn' = (closure' thn n) in
      let els' = (closure' els n) in
        [(If (head cnd') (head thn') (head els'))] 
        
closure' (Set var e) n =
  [(Set var (head (closure' e n)))]

closure' (DefineProc var vars (Let binding (Lambda vars' exp))) n =
  let exp' = closure' (Lambda vars' exp) n in
    if length exp' == 2
    then
      let lamName = getLambdaName (head (tail exp'))
          fvs = getFvs (head (tail exp')) in
        [DefineProc var vars (Let binding (head (tail exp')))] ++ [(DefineProc (Var lamName) fvs (head exp'))]
    else [(DefineProc var vars (head exp'))]

closure' (DefineProc var vars (Lambda vars' exp)) n =
  let exp' = closure' (Lambda vars' exp) n in
    if length exp' == 2
    then
      let closuree = head (tail exp')
          lamName = getLambdaName closuree
          fvs = getFvs (head (tail exp')) in
        [DefineProc var vars (head (tail exp'))] ++ [(DefineProc (Var lamName) fvs (head exp'))]
    else [(DefineProc var vars (head exp'))]
    
closure' (DefineProc var vars exp) n =
  [(DefineProc var vars (head (closure' exp  n)))]
-- map lambda x: x+1 (list 2 3 4)
-- (define (x r) (+ x 1))
-- map x (list 23 4)
closure' (Application op (x:xs)) n =
  case op of
    (Varexp (Var "map")) ->
      case x of
        (Lambda vars exp) ->
          let closuree = head (tail (closure' x n))
              closrName = getLambdaName closuree
              fvs = getFvs closuree
              exps = [Varexp (Var closrName)] ++ closure xs n
              fn = DefineProc (Var closrName) fvs closuree in
            [fn, Application (Varexp (Var "map")) exps]
    _->
      [Application op (x:xs)]
            
closure' (Let [Binding v e] body) n =
  let bdy = (closure' body n) in 
    if length bdy == 2
    then (tail bdy) ++ [(Let [Binding v e] (head bdy))]
    else [(Let [Binding v e] (head bdy))]
    
closure' (Cond cnds) n =
  let cnds' = makeCnds cnds n in
    [Cond cnds']

closure' (Begin exps) n =
  let bgns = map (\x -> closure' x n) exps
      bgns' = concat bgns in
    [Begin bgns']
closure' exp n = [exp]

makeLets :: Exp -> [Var] -> Var -> Int -> Exp
makeLets exp [] _ n = exp
makeLets exp (x:xs) env n =
  Let [Binding (Varexp x) (TupleRef (Varexp env) (Int n))] (makeLets exp xs env (n+1))

freeVariables :: [Var] -> Exp -> [Var]
freeVariables vars (Set (Varexp (Var varName)) exp) =
  if Var varName `elem` vars then [] else [Var varName]

freeVariables vars (Prim _ (Varexp (Var e1)) (Varexp (Var e2))) =
  let fv1 = if Var e1 `elem` vars then [] else [Var e1]
      fv2 = if Var e2 `elem` vars then [] else [Var e2]
  in fv1 ++ fv2

freeVariables vars (Prim _ (Varexp (Var e1)) e2) =
  let fvs = freeVariables vars e2
      fvs2 = if Var e1 `elem` vars then [] else [Var e1]
  in
    fvs ++ fvs2
                     
freeVariables vars (If cnd thn els) =
  freeVariables vars cnd ++ freeVariables vars thn ++ freeVariables vars els

freeVariables vars (Lambda vars' exp) =
  filter (`notElem` vars') (freeVariables vars exp)

freeVariables vars (Let [Binding var exp] body) =
  freeVariables vars exp ++ freeVariables vars body
  

freeVariables _ _ = []

getLambdaName :: Exp -> String
getLambdaName (Closure (Int arity) (Varexp (Var fn)) fvs) =
  fn

getFvs :: Exp -> [Var]
getFvs (Closure (Int arity) (Varexp (Var fn)) fvs) =
  fvs
makeCnds :: [Cnd] -> Int -> [Cnd]
makeCnds (x:xs) n =
  case x of
    Cnd cnd exp ->
      [Cnd (head (closure' cnd n)) (head (closure' exp n))] ++ makeCnds xs (n+1)
    Else exp ->
      [Else (head (closure' exp n))]
      
  
