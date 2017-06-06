module Main where

import System.Environment
import System.Exit
import Data.Tree

import Parser
import Types
import SemanticChecks
import Typecheck
import GenerateMaps

main :: IO ()
main = do
  a <- getArgs
  input <- readFile (head a)
  let ast = parse input
  case performSemanticChecks ast of
    Left err -> putStrLn err
    Right ct -> case annotateAST ast ct of
      Left err   -> putStrLn err
      Right ast' -> putStrLn $ show (implMap ast')
