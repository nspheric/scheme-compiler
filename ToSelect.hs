module ToSelect where

import Parser (
  Binding(Binding),
  Exp(Application, Let, Prim, If, Varexp, Bool, DefineProc, Lambda, Int, Set, Closure, Tuple, TupleRef, Cond, Cons, Nil, FunRef, Quote, Begin, ListExp),
  Operator(Plus, Minus, Less, Greater),
  Var(Var),
  Cnd(Cnd, Else),
  lexer,
  toAst)

import Desugar (desugar)

import ToAnf ( toAnf, revealFunctions )

import ClosureConversion (closure)

data Argument =
  Immediate String
  | Reg String
  | Memory String
  | Deref String Int
  | Memorytup String
  deriving Show

data Instruction =
  Addq Argument Argument
  | Subq Argument Argument
  | Negq Argument
  | Movq Argument Argument
  | Pushq Argument
  | Popq Argument
  | Callq String
  | Retq
  | Jmp String
  | Xorq Argument Argument
  | Cmpq Argument Argument
  | Setl Argument
  | Movzbq Argument Argument
  | Leaq String Argument
  | Label String
  | Je String
  | Jl String
  | Jg String
  | MemoryTup Argument Argument
  | Memoryfn String
  deriving Show
  

registers :: [String]
registers = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
  
toselect' :: [Exp] -> Int -> [Instruction]
toselect' [] _ = []
toselect' (x:xs) n =
  toselect [x] n  ++ toselect' xs (n + 1)
  
toselect :: [Exp] -> Int -> [Instruction]
toselect [(Closure (Int arity) lambda fvs)] n' =
   let tmp = "closure_" ++ show n' in
    let arityBits = tobinary' arity 5
        fvsexps = map (\x -> (Varexp x)) fvs
        ptrMask = getPointMask' fvsexps
        len = length fvs
        lenbits = tobinary' len 6
        iscopied = [1]
        tag = binaryToDecimal (arityBits ++ ptrMask ++ lenbits ++ iscopied)
        nnn = show (8 * (len + 1))
        
    in
      [Movq (Memory "free_ptr(%rip)") (Reg "%r11"),
       Movq (Immediate (show (8 * (len + 1)))) (Memory "free_ptr(%rip)"),
       Movq (Immediate nnn) (Memory "0(%r11)"),
       Movq (Reg "%r11") (Memory tmp)] 
 
toselect [(DefineProc (Var var) vars exp)] n' =
  let diff = (length registers) - (length vars) in
    let regs = take (diff + 1) registers in
      let movqs = map (\(a,b) -> (Movq (Reg a) (Memory (getVar b)))) $ zip regs vars in
        let movqs' = map (\a -> (Movq (Memory (getVar a)) (Reg "%rax"))) vars in
          [Label (var ++ "start")] ++ movqs ++ movqs' ++ [Jmp (var ++ "conclusion")] ++ toselect [exp] n'
          

toselect [If (Varexp (Var v)) thn els] n' =
   [Cmpq (Memory v) (Reg "%rsi"),
    (Setl (Reg "%al")),
     Movzbq (Reg"%al") (Reg "%rsi"),
    Cmpq (Immediate "$1") (Reg "%rsi"),
    Je blk,
    Jmp blk2,
    Label blk] ++ toselect [thn] n' ++ [Label blk2] ++ (toselect [els] n') ++ [Jmp "conclusion"]
   where
     blk = "block" ++ show n'
     blk2 = "block" ++ show (n'+1)

toselect [Cond (x:xs)] n' =
  case x of
    (Cnd (Application (FunRef (Var name) n)  args) thn) ->
      let app = toselect [(Application (FunRef (Var name) n) args)] n' in
        let outputvar = getMemoryName (last app) in
          app ++ [Cmpq (Immediate "$1") (Memory outputvar), Je ("block" ++ show n'), Jmp ("block" ++ show (n'+1)), Label ("block" ++ show n')] ++ toselect [thn] (n'+2) ++ [Label ("block" ++ show (n'+1))] ++ toselect [Cond xs] (n' + 2)
    Else exp ->
      toselect [exp] n'
          
toselect [Int n] n' =
  [Movq (Immediate ("$" ++ show n)) (Reg "%rdi"),
   Callq "print_int"]

toselect [Varexp (Var v)] n' =
  [Movq (Memory v) (Reg "%rdi"),
   Callq "print_int"]
  
toselect [Set (Varexp (Var v)) (Int n)] n' =
  [Movq (Immediate ("$" ++ show n)) (Memory v)]

toselect [Set (Varexp (Var v)) (Prim Plus (Varexp (Var v')) (Varexp (Var v'')))] n' =
  [Movq (Memory v'') (Reg "%rax"),
   Subq (Reg "%rax") (Memory v)]

toselect [Set (Varexp (Var v)) (Prim Plus (Int n) (Int n2))] n' =
  [Movq (Immediate ("$" ++ show n2)) (Reg "%rax"),
   Movq (Immediate ("$" ++ show n)) (Memory v),
   Addq (Reg "%rax") (Memory v)]

toselect [Set (Varexp (Var v)) (Prim Plus (Varexp (Var v')) (Int n))] n' =
  [Movq (Immediate ("$" ++ show n)) (Reg "%rax"),
   Addq (Reg "%rax") (Memory v)]


toselect [Set (Varexp (Var v)) (Prim Plus (Int n) (Varexp (Var v')))] n' =
  [Movq (Immediate ("$" ++ show n)) (Reg "%rax"),
   Addq (Reg "%rax") (Memory v)]


toselect [Set (Varexp (Var v)) (Prim Minus (Int n) (Int n2))] n' =
  [Movq (Immediate ("$" ++ show n2)) (Reg "%rax"),
   Movq (Immediate ("$" ++ show n)) (Memory v),
   Subq (Reg "%rax") (Memory v)]

toselect [Set (Varexp (Var v)) (Prim Minus (Varexp (Var v')) (Int n))] n' =
  [Movq (Immediate ("$" ++ show n)) (Reg "%rax"),
   Subq (Reg "%rax") (Memory v)]


toselect [Set (Varexp (Var v)) (Prim Minus (Int n) (Varexp (Var v')))] n' =
  [Movq (Immediate ("$" ++ show n)) (Reg "%rax"),
   Subq (Reg "%rax") (Memory v)]
  
toselect [Let [(Binding (Varexp (Var v)) (TupleRef (Varexp (Var e)) (Int e2)))] body] n' =
  [Movq (Memory e) (Reg "%r11"),
         Movq (Memorytup ("8(" ++ show (e2 + 1) ++ "(%r11)")) (Memory e)] ++ toselect [body] n'
  
toselect [Application x []] n' = []
toselect [Application (FunRef (Var op) n) exps] n' =
  let fn = toselectfn [(FunRef (Var op) n)] ("tmpapp" ++ show n) n'
      mvs = map (\(x,y) -> Movq (toin x) (Reg y)) $ zip exps registers in
    fn ++ mvs ++ [Callq ("*" ++ op)] ++ [Movq (Reg "%rax") (Memory ("tmpapp" ++ show n))]
  
toselect [(Prim Plus (Int n) (Int n2))] n' =
  [Movq (Immediate ("$" ++ show n2)) (Reg "%rax"),
   Addq (Immediate ("$" ++ show n)) (Reg "%rax")]

toselect [(Prim Plus (Varexp (Var v')) (Int n))] n' =
  [Movq (Immediate ("$" ++ show n)) (Reg "%rax"),
   Addq (Reg "%rax") (Memory v')]


toselect [(Prim Plus (Int n) (Varexp (Var v')))] n' =
  [Movq (Immediate ("$" ++ show n)) (Reg "%rax"),
   Addq (Reg "%rax") (Memory v')]

toselect [(Prim Plus (Varexp (Var v')) (Varexp (Var v'')))] n' =
  [Movq (Memory v'') (Reg "%rax"),
   Addq (Reg "%rax") (Memory v')]
  

toselect [(Prim Plus (Varexp (Var v)) (Prim Plus (Varexp (Var v')) (Varexp (Var v'''))))] n' =
  [Movq (Memory v''') (Reg "%rax"),
   Addq (Memory "%rax") (Memory v'),
   Addq (Memory v) (Reg "%rax")]

toselect [(Prim Less (Int n) (Int n2))] n' =
  [Cmpq (Immediate ("$" ++ show n2)) (Immediate ("$" ++ (show n))),
   (Setl (Reg "%al")),
   Movzbq (Reg"%al") (Reg "%rsi"),
   Cmpq (Immediate "$1") (Reg "%rsi"),
   Je blk,
   Jmp blk2,
   Label blk]
  where
    blk = "block" ++ (show n')
    blk2 = "block" ++ (show n')
    
toselect [(Let [Binding (Varexp (Var var)) (Prim Less (Int n) (Int n''))] (If (Varexp (Var cnd)) thn els))] n' =
  [Movq (Immediate (show n)) (Memory var), Cmpq (Immediate (show n'')) (Memory var),
   Setl (Reg "%al"),
   Movzbq (Reg "%al") (Reg "%rsi"),
   Cmpq (Immediate "$1") (Reg "%rsi")] ++ [Je ("blk" ++ show n)] ++ [Jmp ("blk" ++ show (n+1))] ++ [Label ("blk" ++ show n)] ++  toselect [thn] n' ++  [(Label ("blk" ++ show (n+1)))] ++ toselect [els] n'

toselect [(Let [Binding (Varexp (Var var)) (Application (FunRef (Var op) n) exps)] body)] n' =
  let fn = toselectfn [(FunRef (Var op) n)] var n'
      mvs = map (\(x,y) -> Movq (toin x) (Reg y)) $ zip exps registers in
    fn ++ mvs ++ [Callq ("*" ++ op)] ++ [Movq (Reg "%rax") (Memory var)] ++ toselect [body] n'
    
toselect [(Let [Binding (Varexp (Var var)) (If (Bool b) thn els)] body)] n' =
   [ Movq (tobool (Bool b)) (Reg "%rsi"),
    Cmpq (Immediate "$1") (Reg "%rsi"),
    Je blk,
    Jmp blk2,
    Label blk] ++ toselect [(Let [Binding (Varexp (Var var)) thn] body)] n' ++ [Label blk2] ++ (toselect [(Let [Binding (Varexp (Var var)) els] body)] n') ++ [Jmp "conclusion"]
   where
     blk = "block" ++ show n'
     blk2 = "block" ++ show (n'+1)
toselect [(Let [Binding (Varexp (Var var)) (If (Varexp (Var var')) thn els)] body)] n' =
  [Cmpq (Memory var') (Reg "%rsi"),
    (Setl (Reg "%al")),
     Movzbq (Reg"%al") (Reg "%rsi"),
    Cmpq (Immediate "$1") (Reg "%rsi"),
    Je blk,
    Jmp blk2,
    Label blk] ++ toselect [(Let [Binding (Varexp (Var var)) thn] body)] n' ++ [Label blk2] ++ (toselect [(Let [Binding (Varexp (Var var)) els] body)] n') ++ [Jmp "conclusion"]
   where
     blk = "block" ++ show n'
     blk2 = "block" ++ show (n'+1)

toselect [Let [Binding (Varexp (Var var)) (Int n)] body] n' =
  [Movq (Immediate (show n)) (Memory var)] ++  toselect [body] n' 

toselect [Let [Binding (Varexp (Var var)) (Varexp (Var var'))] body] n' =
  [Movq (Memory var') (Reg "%rsi"), (Movq (Reg "%rsi") (Memory var))] ++ toselect [body] n'

toselect [Let [Binding var exp] body] n' =
  let ss = toselect [exp] n' in
    let ss'' = toselect [body] n' in
        ss''
        
toselect [(Cons e e2)] n' =
   let len = 2
       lenbits = tobinary' len 6
       ptrMask = getPointMask' [e,e2]
       vecname = "vecname" ++ show n'
       iscopied = [1]
       counters = makecounters len 0
       bits = (ptrMask ++ lenbits ++ iscopied)
       tag = binaryToDecimal bits (length bits - 1)
       makesets = map (\(x, n'') -> 
                             [ Movq (Memory vecname) (Reg "%r11")
                             , Movq (toin x)
                                    (Memory ("8(" ++ show ((getNum n'') + 1) ++ "(%r11)"))
                             , Movq (Immediate "$0") 
                                    (Memory ("vectorset" ++ show n''))
                             ]) 
                         $ zip [e,e2] counters
       makesets' = concat makesets
          in
            [ Movq (Memory "free_ptr(%rip)") (Reg "%r11")
            , Movq (Immediate (show (8 * (len + 1)))) (Memory "free_ptr(%rip)")
            , Movq (Immediate (show tag)) (Memory ("0(%r11)"))
            , Movq (Reg "%r11") (Memory vecname)] ++ makesets' ++ [ Movq (Memory vecname) (Reg "%r11") ] ++ [ Movq (Memory ("vectorset" ++ show n')) (Reg "%rdi") ] ++ [ Callq ("*" ++ "fnname" ++ show n') ] ++ [ Movq (Reg "%rax") (Memory ("callq" ++ show n')) ]

toselect [(Tuple exps)] n' =
   let len = length exps
       lenbits = tobinary' len 6
       ptrMask = getPointMask' exps
       vecname = "vecname" ++ show n'
       iscopied = [1]
       counters = makecounters len 0
       tag = binaryToDecimal (ptrMask ++ lenbits ++ iscopied) 0
       makesets = map (\(x, n'') -> 
                             [ Movq (Memory vecname) (Reg "%r11")
                             , Movq (toin x)
                                    (Memory ("8(" ++ show ((getNum n'') + 1) ++ "(%r11)"))
                             , Movq (Immediate "$0") 
                                    (Memory ("vectorset" ++ show n''))
                             ]) 
                         $ zip exps counters
       makesets' = concat makesets
          in
            [ Movq (Memory "free_ptr(%rip)") (Reg "%r11")
            , Movq (Immediate (show (8 * (len + 1)))) (Memory "free_ptr(%rip)")
            , Movq (Immediate (show tag)) (Memory ("0(%r11)"))
            , Movq (Reg "%r11") (Memory vecname)] ++ makesets' ++ [ Movq (Memory vecname) (Reg "%r11") ] ++ [ Movq (Memory ("vectorset" ++ show n')) (Reg "%rdi") ] ++ [ Callq ("*" ++ "fnname" ++ show n') ] ++ [ Movq (Reg "%rax") (Memory ("callq" ++ show n')) ]
            
toselect [(Quote n')] n = toselect [n'] n
toselect [Begin (x:xs)] n =
  toselect [x] n ++ toselect' xs n
toselect [Nil] n = [(Movq (Immediate "$0") (Memory ("nil"++show n)))]

toselect [(Bool b)] n =
  [Movq (tobool (Bool b)) (Memory ("bool"++ show n))]

toselect [(ListExp exps)] n =
  let desugar' = desugar [(ListExp exps)] in
    let anf' = toAnf (revealFunctions desugar') in
      let clsr = closure anf' 0 in
        toselect clsr n
toselectfn :: [Exp] ->  String -> Int -> [Instruction]
toselectfn [(FunRef (Var op) n)] var n' =
  [Leaq (op ++ "(%rip)") (Memory var)]
  
getNum :: Exp -> Int
getNum (Int n) = n

getVar :: Var -> String
getVar (Var v) = v

getVarName :: Exp -> String
getVarName (Varexp (Var e)) =
  e

tobinary' ::  Int -> Int -> [Int]
tobinary' n n' =
  let bits = reverse (tobinary n)
      diff = n' - (length bits)
  in
    replicate diff 0 ++ bits
             
    
tobinary :: Int -> [Int]
tobinary 1 = [1]
tobinary n =
  let n' = n `div` 2 in
    let bit = n `mod` 2 in
      [bit] ++ tobinary n'

getPointMask' :: [Exp] -> [Int]
getPointMask' [] = []
getPointMask' (x:xs) =
  case x of
    Tuple exps ->
      1 : getPointMask' xs
    _ ->
      0 : getPointMask' xs

binaryToDecimal [] n = 0
binaryToDecimal (x:xs) n =
  x * (2^n) + rest
  where
    rest = binaryToDecimal xs (n - 1)


makecounters :: Int -> Int -> [Exp]
makecounters n counter =
  if counter >= n
  then []
  else [Int counter] ++ makecounters n (counter + 1)


toin :: Exp -> Argument
toin (Varexp (Var var)) =
  Memory var

toin (Int n) =
  Immediate ("$" ++ show n)

getMemoryName :: Instruction -> String
getMemoryName (Movq (Reg r) (Memory m)) =
  m

tobool :: Exp -> Argument
tobool (Bool True) =
  Immediate "$1"

tobool (Bool False) =
  Immediate "$0"
