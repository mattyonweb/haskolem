module Parser where

import Text.ParserCombinators.ReadP
import Control.Monad
import Engine

compile = readP_to_S

makeStr :: Char -> String
makeStr c = c:""

ws :: ReadP ()
ws = do many (choice (map char [' ','\n'])) ;
        return ()

variable :: ReadP Expr
variable = (V . makeStr) <$> choice (map char "abcdefgvuwxyz")

negation :: ReadP Expr -> ReadP Expr
negation p = do
  choice (map char "~!¬")
  x <- p
  return $ Not x

simpleTerm = maybeParens (negation variable <++ variable)

-------------------------------------------------------------

quantifier :: ReadP (Expr -> Expr -> Expr)
quantifier = (Exists <$ choice [string "Exists ", string "€", string "∃"]) <++
             (Forall <$ choice [string "Forall ", string "∀"])


operator :: ReadP (Expr -> Expr -> Expr)
operator = (And <$ choice [string "&", string "&&", string "∧"]) <++
           (Or  <$ choice [string "|", string "||", string "∨"])

-------------------------------------------------------------

parens p = (between (string "(") (string ")") p)

maybeParens p =
  parens p <++
  p
  
expr = maybeParens quantified <++ maybeParens propositional

propositional = do
  res <- chainl1 (parens propositional <++ simpleTerm <++ maybeParens quantified) operator ;
  return res

quantified = do
  neg   <- option Nothing (do choice (map char "~!¬"); return (Just Not)) ;
  quant <- (quantifier <*>
             (do v <- variable; skipSpaces; return v) <*> expr) ;
    
  case neg of
    Nothing  -> return quant
    (Just _) -> return (Not $ quant)


-------------------------------------------------------------
  
data Test = Test String Expr

tests = [
  
  Test "¬∀a a" (Not (Forall (V "a") (V "a"))),
  Test "∀a ¬∃y a∨b" (Forall (V "a") (Not (Exists (V "y") (And (V "a") (V "b")))))
  ]

-------------------------------------------------------------

runParser = fst . last . compile expr
  
