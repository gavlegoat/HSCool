{-
Execute code which has passed typechecking and semantic checks.
-}

module Interpreter (evalProgram) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.IO.Class
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
                           , stackSize :: Int
                           , heapCounter :: CoolAddress
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
                         , stackSize = 0
                         , heapCounter = 0
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

eqPure :: CoolValue -> CoolValue -> CoolValue
eqPure (CoolInt i1)        (CoolInt i2)        = CoolBool $ i1 == i2
eqPure (CoolString _ s1)   (CoolString _ s2)   = CoolBool $ s1 == s2
eqPure (CoolBool b1)       (CoolBool b2)       = CoolBool $ b1 == b2
eqPure (CoolObject i1 _ _) (CoolObject i2 _ _) = CoolBool $ i1 == i2
eqPure Void                Void                = CoolBool True
eqPure _                   _                   = CoolBool False

ltPure :: CoolValue -> CoolValue -> CoolValue
ltPure (CoolInt i1)      (CoolInt i2)      = CoolBool $ i1 < i2
ltPure (CoolString _ s1) (CoolString _ s2) = CoolBool $ s1 < s2
ltPure (CoolBool b1)     (CoolBool b2)     = CoolBool $ not b1 && b2
ltPure _                 _                 = CoolBool False

lePure :: CoolValue -> CoolValue -> CoolValue
lePure a b = case eqPure a b of
  CoolBool True  -> CoolBool True
  CoolBool False -> case ltPure a b of
    CoolBool True  -> CoolBool True
    CoolBool False -> CoolBool False

-- The following functions handle internal definitions

internalCopy :: EvalM CoolValue
internalCopy = do
  st <- get
  case so st of
    CoolInt i      -> return $ CoolInt i
    CoolString l s -> return $ CoolString l s
    CoolBool b     -> return $ CoolBool b
    CoolObject     -> return $ undefined
    _ -> error "Internal: self object is not an object"

internalTypeName :: EvalM CoolValue
internalTypeName = do
  st <- get
  case so st of
    CoolInt _        -> return $ CoolString 3 "Int"
    CoolString _ _   -> return $ CoolString 6 "String"
    CoolBool _       -> return $ CoolString 4 "Bool"
    CoolObject _ t _ -> return $ CoolString (length t) t
    _ -> error "Internal: self object is not an object"

internalInInt :: EvalM CoolValue
internalInInt = undefined

internalInString :: EvalM CoolValue
internalInString = undefined

internalOutInt :: EvalM CoolValue
internalOutInt = do
  st <- get
  case Map.lookup "x" (env st) of
    Nothing -> error "Internal: argument to IO.out_int not found (env)"
    Just lo -> case Map.lookup lo (store st) of
      Just (CoolInt i) -> liftIO (putStr (show i)) >> return (so st)
      _ -> error "Internal: bad argument to IO.out_int"

internalOutString :: EvalM CoolValue
internalOutString = do
  st <- lift get
  case Map.lookup "x" (env st) of
    Nothing -> error "Internal: argument to IO.out_string not found (env)"
    Just lo -> case Map.lookup lo (store st) of
      Just (CoolString _ s) -> liftIO (putStr s) >> return (so st)
      _ -> error "Internal: bad argument to IO.out_string"

internalConcat :: EvalM CoolValue
internalConcat = do
  st <- lift get
  case so st of
    CoolString l1 s1 -> case Map.lookup "s" (env st) of
      Just ind -> case Map.lookup ind (store st) of
        Just (CoolString l2 s2) -> return $ CoolString (l1 + l2) (s1 ++ s2)
        _ -> error "Internal: bad argument to String.concat"
      _ -> error "Internal: bad argument to String.concat"
    _ -> error "Internal: String.concat called on non-string"

internalLength :: EvalM CoolValue
internalLength = do
  st <- lift get
  case so st of
    CoolString l _ -> return $ CoolInt $ fromIntegral l
    _ -> error "Internal: String.length called on non-string"

internalSubstr :: EvalM CoolValue
internalSubstr = do
  st <- lift get
  case so st of
    CoolString l s ->
      let iloc = Map.lookup "i" (env st)
          lloc = Map.lookup "l" (env st) in
      case (iloc, lloc) of
        (Just iind, Just lind) ->
          let iv = Map.lookup iind (store st)
              lv = Map.lookup lind (store st) in
          case (iv, lv) of
            (Just (CoolInt iv'), Just (CoolInt lv')) ->
              let ival = fromIntegral iv'
                  lval = fromIntegral lv' in
              if (ival < 0 || lval < 0 || ival + lval > l)
                 then throwError "ERROR: 0: Substring out of range"
                 else return $ CoolString lval (take lval $ drop ival s)
            _ -> error "Internal: args to String.substr not found in store"
        _ -> error "Internal: args to String.substr not found in env"
    _ -> error "Internal: String.substr called on non-string"

internal :: String -> EvalM CoolValue
internal fname = case fname of
  "abort"      -> throwError "abort"
  "copy"       -> internalCopy
  "type_name"  -> internalTypeName
  "in_int"     -> internalInInt
  "in_string"  -> internalInString
  "out_int"    -> internalOutString
  "out_string" -> internalOutString
  "concat"     -> internalConcat
  "length"     -> internalLength
  "substr"     -> internalSubstr

-- Get a fresh location in the store
getNewLoc :: EvalM CoolAddress
getNewLoc = do
  st <- get
  put (st { heapCounter = heapCounter st + 1 })
  return $ heapCounter st

-- This function is used to take care of all of the dispatch cases
dispatch :: Int -> CoolValue -> String -> String -> [CoolValue] ->
            EvalM CoolValue
dispatch line val typ method args = do
  st <- get
  if stackSize st > 1000
     then throwError "ERROR: " ++ show line ++ ": stack overflow" else do
    put (st { stackSize = stackSize st + 1 })
    maps <- ask
    case Map.lookup (typ, method) (implMap maps) of
      Nothing -> error "Internal: method " ++ method ++ " not found"
      Just (args, body) -> do
        -- Get a fresh set of locations for storing the arguments
        newlocs <- replicateM (length args) getNewLoc
        case val of
          Void -> throwError "ERROR: " ++ show line ++ ": Dispatch on void"
          CoolString _ _ -> if typ == "String"
                            then undefined
                            else error "Internal in dispatch"
          CoolObject _ cn av -> if typ == cn
                                then undefined
                                else error "Internal in dispatch"
          _ => error "Internal in dispatch"
        -- add each argument to the store and the environment
        -- evaluate body in the new environment
        -- remove arguments from the store and env

-- This is the main evaluation function for the interpreter. A Cool program is
-- run by calling this function with the expression
-- `DynamicDispatch (New "Main") "main" []`
evalExpr :: TypeExpr -> EvalM CoolValue
evalExpr expr@(AnnFix (TypeAnn line typ, e)) = case e of
  Let bs body -> undefined
  Case body bs -> undefined
  Assign id e -> do
    v1 <- evalExpr e
    st <- get
    case Map.lookup (idName id) (env st) of
      Just loc -> put (st { store = Map.insert loc v1 (store st) }) >> return v1
      Nothing  -> error "Internal: Assignment to non-existant variable"
  DynamicDispatch e m ps -> do
    v <- evalExpr e
    as <- mapM evalExpr ps
    case v of
      CoolString _ _ -> dispatch line v "String" (idName m) as
      CoolObject _ t _ -> dispatch line v t (idName m) as
      Void -> throwError $ "ERROR: " ++ show line ++ ": dispatch on void"
      _ -> error "Internal: dispatch on bad value"
  StaticDispatch e t m ps -> do
    v <- evalExpr e
    as <- mapM evalExpr ps
    case v of
      Void -> throwError $ "ERROR: " ++ show line ++ ": dispatch on void"
      _ -> dispatch line v (idName t) (idName m) as
  SelfDispatch m ps -> do
    st <- get
    as <- mapM evalExpr ps
    case so st of
      CoolString _ _ -> dispatch line (so st) "String" (idName m) as
      CoolObject _ t _ -> dispatch line (so st) t (idName m) as
      _ -> error "Internal: self dispatch on bad object"
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
  Le x y -> liftM2 lePure (evalExpr x) (evalExpr y)
  Lt x y -> liftM2 ltPure (evalExpr x) (evalExpr y)
  Eq x y -> liftM2 eqPure (evalExpr x) (evalExpr y)
  Not e -> liftM notPure $ evalExpr e
  Negate e -> liftM negatePure $ evalExpr e
  IntConst i -> return $ CoolInt i
  StringConst s -> return $ CoolString (length s) s
  Id id -> do
    st <- get
    case Map.lookup (idName id) (env st) of
      Nothing  -> error "Internal error: Problem with ID lookup (env)"
      Just loc -> case Map.lookup loc (store st) of
        Nothing  -> error "Internal error: Problem with ID lookup (store)"
        Just val -> return val
  BoolConst b -> return $ CoolBool b
  Internal fname -> internal fname

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
