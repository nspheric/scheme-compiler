{
module Parser where

import Data.Char (isSpace, isAlpha, isDigit, isAlphaNum)
}

%name toAst
%tokentype { Token }
%error { parseError }

%token
    let            { TokenLet }
    if             { TokenIf }
    quote          { TokenQuote }
    set            { TokenSet }
    lambda         { TokenLambda }
    letrec         { TokenLetrec }
    begin          { TokenBegin }
    macro          { TokenMacro }
    '('            { TokenLParen }
    ')'            { TokenRParen }
    '+'            { TokenPlus }
    '-'            { TokenMinus }
    '<'            { TokenLess }
    '>'            { TokenGreater }
    '='            { TokenEqual }
    true            { TokenTrue }
    false            { TokenFalse }
    and            { TokenAnd }
    or             { TokenOr }
    var            { TokenVar $$ }
    int            { TokenInt $$ }
    define         { TokenDefine }
    tuple          { TokenTuple }
    tupleref       { TokenTupleRef }
    cond           { TokenCond }
    else           { TokenElse }
    cons           { TokenCons}
    nil            { TokenNil }
    list           { TokenList }
    car            { TokenCar }
    cdr             { TokenCdr }
    case            { TokenCase }
when            { TokenWhen }
unless          { TokenUnless }
while           { TokenWhile }
not             { TokenNot }
funref          { Tokenfunref }
%%

Program : Exps { $1 }

Exp : true { Bool True }
    | false { Bool False }
    | nil { Nil }
    | int { Int $1 }
    | Var { Varexp $1 }
    | '(' funref Var int ')' { FunRef $3 $4 }
    | prim { $1 }
    | '(' let '(' bindings ')' Exp ')' { Let $4 $6 }
    | '(' if Exp Exp Exp ')' { If $3 $4 (Just $5) }
    | '(' if Exp Exp ')'     { If $3 $4 Nothing }
    | '(' quote Exp ')' { Quote $3 }
    | '(' begin Exps ')' { Begin $3 }
    | '(' set Exp Exp ')' { Set $3 $4 }
    | '(' lambda '(' params ')' Exp ')' { Lambda $4 $6 }
    | '(' letrec '(' bindings ')' Exp ')' { Letrec $4 $6 }
    | '(' macro Exp Exp ')' { SchemeMacro $3 $4 }
    | '(' define '(' Var params ')' Exp ')' { DefineProc $4 $5 $7 }
    | '(' define Var Exp ')'                { DefineExp $3 $4 }
    | '(' cond cndexps ')'                { Cond $3 }
    | '(' case Exp clauses ')'                { Case $3 $4 }
    | '(' when Exp Exp ')'                { When $3 $4 }
    | '(' unless Exp Exp ')'                   { Unless $3 $4 }
    | '(' while Exp Exp ')'                   { While $3 $4 }
    | '(' Exp Exps ')'                    { Application $2 $3 }


Var : var { Var $1 }
    | lambda { Var "lambda"}
    | define { Var "define" }
    | quote { Var "quote" } 
    | cond { Var "cond" }
    | begin { Var "begin" }
    | if { Var "if" }
    | begin { Var "begin" }
    | set { Var "set" }
    | else {Var "else"}
    | car { Var "car" }
    | cdr { Var "cdr" }
    | cons { Var "cons" }
    | case { Var "case" }
    | when { Var "when" }
    | unless { Var "unless" }
    | while { Var "while" }
    | not { Var "not" }

Funref : Var int {FunRef $1 $2}

Exps : Exp { [$1] }
     | Exp Exps { $1 : $2 }

prim : '(' '+' Exp Exp ')' { Prim Plus $3 $4 }
     | '(' '-' Exp Exp ')' { Prim Minus $3 $4 }
     | '(' '=' Exp Exp ')' { Prim Equal $3 $4 }
     | '(' and Exp Exp ')' { Prim And $3 $4 }
     | '(' or Exp Exp ')' { Prim Or $3 $4 }
     | '(' '<' Exp Exp ')' { Prim Less $3 $4 }
     | '(' '>' Exp Exp ')' { Prim Greater $3 $4 }
     | '(' cdr Exp ')'     { Cdr $3 }
     | '(' car Exp ')'     { Car $3 }
     | '(' list tupleparams ')' { ListExp $3 }
     | '(' cons Exp Exp ')'    { Cons $3 $4 }
     | '(' tuple tupleparams ')'  { Tuple $3 }
     | '(' tupleref Exp Exp ')'   { TupleRef $3 $4}
     | '(' not Exp ')' { Not $3 }

bindings : binding { [$1] }
         | bindings binding { $1 ++ [$2] }

binding : '(' Exp  Exp ')' {
    Binding $2 $3
}

cndexps : cndexp { [$1] }
       | cndexps cndexp { $1 ++ [$2] }

cndexp : '(' else Exp ')' { Else $3 }
       | '(' Exp Exp ')'  { Cnd $2 $3 }

clauses : clause   { [$1] }
        | clauses clause  { $1 ++ [$2] }

clause : '(' '(' datums ')' Exp ')'  { Clause $3 $5 }

datums : Exp { [$1] }
       | datums Exp { $1 ++ [$2] }


tupleparams : Exp {[$1]}
            | tupleparams Exp { $1 ++ [$2]}

params : Var { [$1] }
       | params Var { $1 ++ [$2] }

{

parseError :: [Token] -> a
parseError _ = error "Parse error"

  
data Exp =
      Bool Bool
    | Varexp Var
    | FunRef Var Int
    | Int Int
    | Prim Operator Exp Exp
    | Let [Binding] Exp
    | Letrec [Binding] Exp
    | If Exp Exp (Maybe Exp)
    | Set Exp Exp
    | Begin [Exp]
    | Not Exp
    | Quote Exp
    | DefineProc Var [Var] Exp
    | DefineExp Var Exp
    | Lambda [Var] Exp
    | SchemeMacro Exp Exp
    | Tuple [Exp]
    | TupleRef Exp Exp
    | ListExp [Exp]
    | Cons Exp Exp
    | Car Exp
    | Cdr Exp 
    | Cond [Cnd]
    | Case Exp [Clauses]
    | Nil
    | When Exp Exp
    | Unless Exp Exp
    | While Exp Exp
    | Application Exp [Exp]
  deriving (Show, Eq)

data Exps = Exps [Exp]
  
data Binding = Binding Exp Exp
  deriving (Show, Eq)
  
data Operator = Plus | Minus | And | Or | Less | Greater | Equal 
  deriving (Show, Eq)

data Var = Var String
  deriving (Show, Eq, Ord)
  
data Cnd =
  Cnd Exp Exp
  | Else Exp
  deriving (Show, Eq)

data Clauses =
  Clause [Exp] Exp
  deriving (Show, Eq)
  
data Token =
      TokenLet
    | TokenIf
    | TokenQuote
    | TokenSet
    | TokenLambda
    | TokenLetrec
    | TokenBegin
    | TokenMacro
    | TokenDefine
    | TokenLParen
    | TokenRParen
    | TokenPlus
    | TokenMinus
    | TokenLess
    | TokenGreater
    | TokenEqual
    | TokenTrue
    | TokenFalse
    | TokenAnd
    | TokenTuple
    | TokenTupleRef
    | TokenOr
    | TokenCond
    | TokenInt Int
    | TokenElse
    | TokenCdr
    | TokenCar
    | TokenList
    | TokenCons
    | TokenNil
    | TokenCase
    | TokenVar String
    | TokenWhen
    | TokenUnless
    | TokenWhile
    | TokenNot
    | Tokenfunref
    deriving (Show, Eq)

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
  | isSpace c = lexer cs
  | isDigit c = lexNum (c:cs)
  | isValidVarChar c = lexVar (c:cs)
lexer ('=':cs) = TokenEqual : lexer cs
lexer ('+':cs) = TokenPlus : lexer cs
lexer ('-':cs) = TokenMinus : lexer cs
lexer ('(':cs) = TokenLParen : lexer cs
lexer (')':cs) = TokenRParen : lexer cs
lexer ('<':cs) = TokenLess : lexer cs
lexer ('>':cs) = TokenGreater : lexer cs
lexer _ = error "Unrecognized character"

isValidVarChar :: Char -> Bool
isValidVarChar c = c == '-' || c == '?' || isAlphaNum c || isAlpha c

lexNum :: String -> [Token]
lexNum cs =
  let (num, rest) = span isDigit cs
   in TokenInt (read num) : lexer rest

lexVar cs =
  case span isValidVarChar cs of
    ("let", rest)    -> TokenLet : lexer rest
    ("if", rest)     -> TokenIf : lexer rest
    ("quote", rest)  -> TokenQuote : lexer rest
    ("set", rest)    -> TokenSet : lexer rest
    ("lambda", rest) -> TokenLambda : lexer rest
    ("letrec", rest) -> TokenLetrec : lexer rest
    ("begin", rest)  -> TokenBegin : lexer rest
    ("macro", rest)  -> TokenMacro : lexer rest
    ("and", rest)    -> TokenAnd : lexer rest
    ("or", rest)     -> TokenOr : lexer rest
    ("true", rest)    -> TokenTrue : lexer rest
    ("false", rest)    -> TokenFalse : lexer rest
    ("define", rest)   -> TokenDefine : lexer rest
    ("tuple", rest)    -> TokenTuple : lexer rest
    ("tupleref", rest) -> TokenTupleRef : lexer rest
    ("cond", rest)       -> TokenCond : lexer rest
    ("else", rest)        -> TokenElse : lexer rest
    ("list", rest)   -> TokenList : lexer rest
    ("cons", rest)  -> TokenCons : lexer rest
    ("car", rest)    -> TokenCar : lexer rest
    ("cdr", rest)    -> TokenCdr : lexer rest
    ("nil", rest)      -> TokenNil : lexer rest
    ("case", rest)     -> TokenCase : lexer rest
    ("while", rest)     -> TokenWhile : lexer rest
    ("when", rest)      -> TokenWhen : lexer rest
    ("unless", rest)     -> TokenUnless : lexer rest
    ("not", rest)       -> TokenNot : lexer rest
    ("funref", rest)   -> Tokenfunref : lexer rest
    (var, rest)      -> TokenVar var : lexer rest

main = getContents >>= print . toAst . lexer
}
