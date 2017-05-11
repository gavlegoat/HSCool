module Main where

import System.Environment
import System.Exit
import Data.Tree

import Parser
import Types
import Typecheck

main :: IO ()
main = do
  a <- getArgs
  input <- readFile (head a)
  let ast = parse input
  case classTree ast of
    Left err -> putStrLn err
    Right ct -> putStrLn . show $ getLineage "Main" ct
