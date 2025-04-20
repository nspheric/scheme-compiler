module Compile where
import System.IO
import Parser (
  Exp(DefineProc),
  lexer,
  toAst
  )
import Desugar (desugar)
import ToAnf (toAnf, revealFunctions)
import ClosureConversion (closure)
import ToSelect (toselect')

compile :: String -> IO ()
compile exp =
  let ast = toAst (lexer exp)
      anf = toAnf (revealFunctions ast)
      closr = closure anf 0
      selects = toselect' closr 0
  in print selects

main :: IO ()
main = do
  s <- readFile "testx.scm"
  compile s

