module Codegen where

import Control.Monad
import Control.Monad.State
import qualified Data.Map as M
import Data.Map (Map)

import LLVM.AST

import Types
import qualified GenerateMaps as G

-- This general setup is taken from the Haskell version of the LLVM tutorial
-- at http://www.stephendiehl.com/llvm/#chapter-3-code-generation

type SymbolTable = Map String Operand

-- Map the names of instructions to their numbers
type Names = Map String Int

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

newtype Codegen a = Codegen { runCodegen :: State CodegenState a }
  deriving (Functor, Applicative, Monad, MonadState CodegenState)

newtype LLVM a = LLVM (State Module a)
  deriving (Functor, Applicative, Monad, MonadState Module)

runLLVM :: Module -> LLVM a -> Module
runLLVM mod (LLVM m) = execState m mod

emptyModule :: String -> Module
emptyModule label = defaultModule { moduleName = label }

addDefn :: Definition -> LLVM ()
addDefn d = do
  defs <- gets moduleDefinitions
  modify $ \s -> s { moduleDefinitions = defs ++ [d] }

-- Define a scheme for combining class and method names to get a globally
-- unique function name.
mangle :: (String, String) -> String
mangle (cl, la) = cl ++ "__" ++ la

-- Add a function definition to the module
define :: Type -> (String, String) -> [(Type, Name)] -> [BasicBlock] -> LLVM ()
define retty label argtys body = addDefn $
  GlobalDefinition $ functionDefaults {
    name = Name (mangle label)
  , parameters = ([Parameter ty nm [] | (ty, nm) <- argtys], False)
  , returnType = retty
  , basicBlocks = body
  }

-- Get a reference to the current block. I'm not sure why the tutorial defines
-- both entry and getBlock, but to make things easier on myself I'll just
-- follow along with that for now.
entry :: Codegen Name
entry = gets currentBlock
getBlock = entry

addBlock :: String -> Codegen Name
addBlock bname = do
  bls <- gets blocks
  ix <- gets blockCount
  nms <- gets names
  let new = emptyBlock ix
      (qname, supply) = uniqueNames bname nms
  modify $ \s -> s { blocks = M.insert (Name qname) new bls
                   , blockCount = ix + 1
                   , names = supply }
  return $ Name qname

-- Change the current block
setBlock :: Name -> Codegen Name
setBlock bname = do
  modify $ \s -> s { currentBlock = bname }
  return bname

modifyBlock :: BlockState -> Codegen ()
modifyBlock new = do
  active <- gets currentBlock
  modify $ \s -> s { blocks = M.insert active new (blocks s) }

current :: Codegen BlockState
current = do
  c <- gets currentBlock
  blks <- gets blocks
  case M.lookup c blks of
    Just x -> return x
    Nothing -> error $ "No such block: " ++ show c

fresh :: Codegen Word
fresh = do
  i <- gets count
  modify $ \s -> s { count = i + 1 }
  return $ i + 1

uniqueName :: String -> Names -> (String, Names)
uniqueName nm ns = case M.lookup nm ns of
  Nothing -> (nm, M.insert nm 1 ns)
  Just ix -> (nm ++ show ix, M.insert nm (ix + 1), ns)

-- Add a (stack-allocated) local variable to the symbol table
assign :: String -> Operand -> Codegen ()
assign var x = do
  lcls <- gets symtab
  modify $ \s -> s { symtab = M.insert var x lcls }

-- Lookup something in the symbol table
getVar :: String -> Codegen Operand
getVar var = do
  syms <- gets symtab
  case M.lookup var  syms of
    Just x -> return x
    Nothing -> error $ "Local variable not in scope: " ++ show var

instr :: Instruction -> Type -> Codegen Operand
instr ins typ = do
  n <- fresh
  let ref = UnName n
  blk <- current
  let i = stack blk
  modifyBlock (blk { stack = (ref := ins) : i })
  return $ LocalReference typ ref

terminator :: Named Terminator -> Codegen (Named Terminator)
terminator trm = do
  blk <- current
  modifyBlock (blk { term = Just trm })
  return trm

add :: Operand -> Operand -> Codegen Operand
add a b = instr $ Add False False a b []

sub :: Operand -> Operand -> Codegen Operand
sub a b = instr $ Sub False False a b []

mul :: Operand -> Operand -> Codegen Operand
mul a b = instr $ Mul False False a b []

div :: Operand -> Operand -> Codegen Operand
div a b = instr $ SDiv False a b []

br :: Name -> Codegen (Named Terminator)
br val = terminator $ Do $ Br val []

cbr :: Operand -> Name -> Name -> Codegen (Named Terminator)
cbr cond tr fl = terminator $ Do $ CondBr cond tr fl []

ret :: Operand -> Codegen (Named Terminator)
ret val = terminator $ Do $ Ret (Just val) []
