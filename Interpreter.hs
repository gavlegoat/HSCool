{-
Execute code which has passed typechecking and semantic checks.
-}

module Interpreter (evalProgram) where

import Control.Monad
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class
import Data.Int
import qualified Data.Map.Strict as Map

import Types
import qualified GenerateMaps as G

type CoolAddress = Int
  
-- The last part of the CoolObject constructor is an association list mapping
-- attribute names to locations in the store. The first argument to the
-- CoolObject is a unique identifier used for comparison
data CoolValue
  = CoolInt Int32
  | CoolString Int String
  | CoolBool Bool
  | CoolObject Int String [(String, CoolAddress)]
  | Void
  deriving (Show, Eq)

-- The environment will be a map from names to CoolAddresses
type CoolEnv = Map.Map String CoolAddress

-- The store will be a map from CoolAddresses to CoolValues
type CoolStore = Map.Map CoolAddress CoolValue

data EvalState = EvalState { env :: CoolEnv
                           , store :: CoolStore
                           , so :: CoolValue
                           }

data EvalConf = EvalConf { classMap :: ClassMap
                         , parentMap :: ParentMap
                         , implMap :: ImplMap
                         , ast :: TypeAST
                         }

initialState :: EvalState
initialState = EvalState { env = Map.empty
                         , store = Map.empty
                         , so = Void
                         }

-- EvalM is the monad in which evaluation takes place. It includes state for
-- storing the environment and store, a reader for storing the class/parent/
-- implementation map, IO for the IO functions and an exception monad for
-- dealing with errors.
type EvalM = ExceptT String (StateT EvalState (ReaderT EvalConf IO))

-- For expression constructors which do not generate errors, cause IO, or
-- require changes to state, we define pure functions which simply map Cool
-- values to Cool values. These can be lifted with liftM to work on
-- ErrorStateIO CoolValue. Some of these "pure" functions call error, but this
-- is only when the error should have been caught in typechecking and indicates
-- a bug in the typechecker rather than in the program being run.

isvoidPure :: CoolValue -> CoolValue
isvoidPure Void = CoolBool True
isvoidPure _    = CoolBool False

notPure :: CoolValue -> CoolValue
notPure (CoolBool b) = CoolBool $ not b
notPure _ = error "Internal: not called on non-boolean"

negatePure :: CoolValue -> CoolValue
negatePure (CoolInt i) = CoolInt (-i)
negatePure _ = error "Internal: negate called on non-integer"

arithOpPure :: (Int32 -> Int32 -> Int32) -> CoolValue -> CoolValue -> CoolValue
arithOpPure op (CoolInt i1) (CoolInt i2) = CoolInt $ op i1 i2
arithOpPure _ _ _ = error "Internal: arithmetic operator called on non-integers"

-- This is the main evaluation function for the interpreter. A Cool program is
-- run by calling this function with the expression
-- `DynamicDispatch (New "Main") "main" []`
evalExpr :: TypeExpr -> EvalM CoolValue
evalExpr expr@(AnnFix (TypeAnn line typ, e)) = case e of
  Let bs body -> undefined
  Case body bs -> undefined
  Assign id e -> undefined
  DynamicDispatch e m ps -> undefined
  StaticDispatch e m t ps -> undefined
  SelfDispatch m ps -> undefined
  If p t f -> do
    val <- evalExpr p
    case val of
      CoolBool b -> if b then evalExpr t else evalExpr f
      _ -> error "Internal: condition in if is non-boolean"
  While p e -> do
    val <- evalExpr p
    case val of
      CoolBool b -> if b then evalExpr e >> evalExpr expr else return Void
      _ -> error "Internal: condition in while is non-boolean"
  Block es -> foldM (\_ -> evalExpr) Void es
  New id -> undefined
  Isvoid e -> liftM isvoidPure $ evalExpr e
  Plus x y -> liftM2 (arithOpPure (+)) (evalExpr x) (evalExpr y)
  Minus x y -> liftM2 (arithOpPure (-)) (evalExpr x) (evalExpr y)
  Times x y -> liftM2 (arithOpPure (*)) (evalExpr x) (evalExpr y)
  Divide x y -> liftM2 (arithOpPure div) (evalExpr x) (evalExpr y)
  Le x y -> undefined
  Lt x y -> undefined
  Eq x y -> undefined
  Not e -> liftM notPure $ evalExpr e
  Negate e -> liftM negatePure $ evalExpr e
  IntConst i -> return $ CoolInt i
  StringConst s -> return $ CoolString (length s) s
  Id id -> do
    st <- lift get
    case Map.lookup (idName id) (env st) of
      Nothing  -> error "Internal error: Problem with ID lookup (env)"
      Just loc -> case Map.lookup loc (store st) of
        Nothing  -> error "Internal error: Problem with ID lookup (store)"
        Just val -> return val
  BoolConst b -> return $ CoolBool b
  Internal -> undefined

-- The main expression which initializes the program: `(new Main).main()`
mainExpr :: TypeExpr
mainExpr = AnnFix (TypeAnn 0 "",
                   DynamicDispatch (AnnFix (TypeAnn 0 "",
                                            New (Identifier 0 "Main")))
                                   (Identifier 0 "main") [])

config :: TypeAST -> EvalConf
config a = EvalConf { classMap = G.classMap a
                    , parentMap = G.parentMap a
                    , implMap = G.implMap a
                    , ast = a
                    }
           
-- Runs a Cool program. The return value indicates whether there was an
-- exception.
evalProgram :: TypeAST -> IO Bool
evalProgram ast = do
  res <- runReaderT (evalStateT (runExceptT (evalExpr mainExpr)) initialState)
                    (config ast)
  case res of
    Left err -> putStrLn err >> return False
    Right _  -> return True

-- evalExpr mainExpr :: ExceptT String (StateT EvalState (ReaderT EvalConf IO)) CoolValue
-- runExceptT (evalExpr mainExpr) :: StateT EvalState (ReaderT EvalConf IO) (Either String CoolValue)
-- evalStateT (runExceptT (evalExpr mainExpr)) initialState :: ReaderT EvalConf IO (Either String CoolValue)
