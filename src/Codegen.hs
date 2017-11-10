module Codegen where

import Control.Monad
import Control.Monad.State
import qualified Data.Map as M
import Data.Map (Map)

import LLVM.AST

import Types
import qualified GenerateMaps as G

type SymbolTable = Map String Operand

data BlockState =
  BlockState { idx :: Int
             , stack :: [Named Instruction]
             , term :: Maybe (Named Terminator)
             } deriving (Show)

data CodegenState =
  CodegenState { currentBlock :: Name
               , blocks :: Map Name BlockState
               , symtab :: SymbolTable
               , blockCount :: Int
               , count :: Int
               , names :: Names
               } deriving (Show)
