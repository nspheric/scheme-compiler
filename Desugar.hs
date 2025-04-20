module Desugar where

-- I ported dr. might's desugarer from his Scheme compiler :)

import Parser (
  Exps(Exps),
  Exp(Varexp, Lambda, Let, Application, Letrec, Set, Begin, If, DefineProc, Cond, Nil, Cons, Tuple, ListExp, Car, Cdr, Prim, Not, Unless, When),
  Binding(Binding),
  Var(Var),
  Cnd(Cnd, Else),
  lexer,
  toAst
  )

{---
def := (define var exp)
    | (define (var <formals>) exp)

<exp> ::= <var>
       | <number>
       | <prim>
       | (quote <literal>)
       | (lambda (<var>*) <exp>)
       | (set <var> <exp>)
       | (if <exp> <exp> <exp>)
       | <prim>
       | (<exp> <exp>*)

<prim> ::= + | < | = | > | cons | vector
---}

desugar :: [Exp] -> [Exp]
desugar [] = []
desugar (x:xs) =
  desugar' x : rest
  where
    rest = desugar xs
    
desugar' :: Exp -> Exp
desugar' (Let bindings body) =
  let formals = map (\x -> getVar x) bindings
      exps = map (\x -> getExp x) bindings
  in
    (Application (Lambda formals (desugar' body)) exps)
    
desugar' (Letrec bindings body) =
  let namings = map (\x -> (Binding (Varexp (getVar x)) (Varexp (Var "#f")))) bindings in
    let sets = map (\x -> (Set (Varexp (getVar x))  (getExp x))) bindings in
      desugar' (Let namings (Begin (sets ++ [body])))

desugar' (Begin exps) =
  desugar' (makeLets exps)
  where
    makeLets :: [Exp] -> Exp
    makeLets [x] = x
    makeLets (x:xs) =
      desugar' (Let [(Binding (Varexp (Var "#f")) x)] e)
      where
        e = makeLets xs
     
desugar' (Application exp exps) =
  Application exp' exps'
  where
    exp' = desugar' exp
    exps' = map desugar' exps

desugar' (Lambda vars body) =
  Lambda vars (desugar' body)

desugar' (Set var exp) =
  Set var (desugar' exp)

desugar' (If cnd thn (Just els)) =
  If (desugar' cnd) (desugar' thn) (Just (desugar' els))

desugar' (If cnd thn Nothing) =
  (If (desugar' cnd) (desugar' thn) Nothing)
  
desugar' (DefineProc var prms exp) =
  DefineProc var prms (desugar' exp)

desugar' (Cond exps) =
  cndToIfs exps 

desugar' (Cons e e2) =
  (Cons (desugar' e) (desugar' e2))

desugar' (Prim op e e2) =
  (Prim op (desugar' e) (desugar' e2))
  
desugar' (ListExp (x:xs)) =
  Cons x  (desugar' (ListExp xs))

desugar' (ListExp []) =
  Nil

desugar' (Car exp) =
  (Car (desugar' exp))

desugar' (Cdr exp) =
  Cdr (desugar' exp)

desugar' (When e e2) =
  (If (desugar' e) (desugar' e2) Nothing)

desugar' (Unless e e2) =
  (If (Not (desugar' e)) (desugar' e2) Nothing)

desugar' e = e

getVar :: Binding -> Var
getVar (Binding (Varexp v) e) = v

getExp :: Binding -> Exp
getExp (Binding v e) = e

cndToIfs :: [Cnd] -> Exp
cndToIfs (x:xs) =
  case x of
    Else e ->
      e
    _ -> (If (getcnd x) (getthn x) (Just (cndToIfs xs)))

getcnd :: Cnd -> Exp
getcnd (Cnd cnd e) = cnd

getthn :: Cnd -> Exp
getthn (Cnd cnd e) = e

