module ParserFile where

import qualified Data.Text as T
import Text.ParserCombinators.ReadP
import Control.Monad
import Parser as P
import Engine

hyp :: ReadP Expr
hyp = do
  string "hyp\n"
  e <- P.expr
  ws
  return e

hyps = manyTill hyp eof

runFileParser = fst . last . compile hyps 



