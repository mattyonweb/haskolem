module Main where

import Engine
import Parser
import ParserFile
import Options.Applicative
import Data.Semigroup ((<>))

data Args = Args
  { fromFile :: String }

sample :: Parser Args
sample = Args
      <$> strOption
          ( long "inputFile"
         <> metavar "FILE"
         <> value ""
         <> help "Target for the greeting" )

runSolver :: Args -> IO ()
runSolver (Args "") = do
  s <- getLine
  solverMultipleIO [runParser s]
  return ()
runSolver (Args fname) = do
  s <- readFile fname
  solverMultipleIO $ runFileParser s
  return ()
  
main :: IO ()
main = runSolver =<< execParser opts
  where
    opts = info (sample <**> helper)
      ( fullDesc
     <> progDesc "MRA Solver"
     <> header "haskolem - a skolemizer" )

-- do
--   s <- getLine ;
--   formulas <- parseFormulas args
--   let formula = (runParser s)
--     in do
--     skolemIO formula
--     return ()
