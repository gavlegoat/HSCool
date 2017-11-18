{-
Execute code which has passed typechecking and semantic checks.
-}

module Interpreter (evalProgram) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Applicative ((<$>))
import Data.Int
import Data.Char
import qualified Data.Map.Strict as Map

import Types
import qualified GenerateMaps as G

-- TODO: Switch to a more realistic model of the heap

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
                           , hp :: CoolAddress   -- The next available heap address
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
                         , hp = 0
                         }

-- EvalM is the monad in which evaluation takes place. It includes state for
-- storing the environment and store, a reader for storing the class/parent/
-- implementation map, IO for the IO functions and an exception monad for
-- dealing with errors.
type EvalM = ExceptT String (StateT EvalState (ReaderT EvalConf IO))

-- For expression constructors which do not generate errors, cause IO, or
-- require changes to state, we define pure functions which simply map Cool
-- values to Cool values. These can be lifted with liftM to work on
-- EvalM CoolValue. Some of these "pure" functions call error, but this
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

compareOpPure :: (Int32 -> Int32 -> Bool) -> CoolValue -> CoolValue -> CoolValue
compareOpPure op (CoolInt i1) (CoolInt i2) = CoolBool $ op i1 i2
compareOpPure _ _ _ = error "Internal: comparison operator called on non-integers"

-- Add a binding
nextAddress :: EvalM CoolAddress
nextAddress = do
  st <- get
  let h = hp st
  if h >= 500000   -- We simulate (badly) running out of heap space
  then throwError "Runtime: Out of heap space"
  else do
    put st { hp = h + 1 }
    return h

-- Create a new variable
bindVar :: String -> CoolValue -> EvalM ()
bindVar s v = do
  st <- get
  h <- nextAddress
  put st { env = Map.insert s h (env st)
         , store = Map.insert h v (store st) }

-- Create a new default value for a variable
defaultValue :: String -> CoolValue
defaultValue "Int" = CoolInt 0
defaultValue "String" = CoolString 0 ""
defaultValue "Bool" = CoolBool False
defaultValue _ = Void

-- Define the equality operator for Cool values
coolEq :: CoolValue -> CoolValue -> CoolValue
coolEq (CoolInt i1)        (CoolInt i2)        = CoolBool $ i1 == i2
coolEq (CoolString _ s1)   (CoolString _ s2)   = CoolBool $ s1 == s2
coolEq (CoolBool b1)       (CoolBool b2)       = CoolBool $ b1 == b2
coolEq Void                Void                = CoolBool True
coolEq (CoolObject i1 _ _) (CoolObject i2 _ _) = CoolBool $ i1 == i2
coolEq _ _ = error "Internal: badly-typed arguments to coolEq"

-- Internal methods
coolLength :: CoolValue -> EvalM CoolValue
coolLength (CoolString i _) = return $ CoolInt $ fromIntegral i
coolLength _ = error "Internal: length called on non-string"

coolSubstr :: Int -> CoolValue -> [CoolValue] -> EvalM CoolValue
coolSubstr line (CoolString len s) [CoolInt i, CoolInt l] =
  if l < 0 || i + l > fromIntegral len
  then throwError $
    "Runtime: " ++ show line ++
    ": Substring of length " ++ show l ++ " at index " ++ show i ++
    " out of bounds for string \"" ++ s ++ "\""
  else return $ CoolString (fromIntegral l)
                           (take (fromIntegral l) $ drop (fromIntegral i) s)
coolSubstr _ _ _ = error "Internal: substr called with bad arguments"

coolConcat :: CoolValue -> [CoolValue] -> EvalM CoolValue
coolConcat (CoolString i1 s1) [CoolString i2 s2] =
  return $ CoolString (i1 + i2) (s1 ++ s2)
coolConcat _ _ = error "Internal: concat called with bad arguments"

coolAbort :: [CoolValue] -> EvalM CoolValue
coolAbort [CoolString _ s] = throwError s
coolAbort _ = error "Internal: abort called with bad arguments"

coolTypeName :: CoolValue -> EvalM CoolValue
coolTypeName (CoolInt _) = return $ CoolString 3 "Int"
coolTypeName (CoolBool _) = return $ CoolString 4 "Bool"
coolTypeName (CoolString _ _) = return $ CoolString 6 "String"
coolTypeName (CoolObject _ t _) = return $ CoolString (length t) t
coolTypeName _ = error "Internal: typename called with bad arguments"

coolCopy :: CoolValue -> EvalM CoolValue
coolCopy v = case v of
  Void -> error "Internal: copy called on void"
  CoolObject id t vs -> undefined
  _ -> return v

coolInString :: EvalM CoolValue
coolInString = do
  s <- liftIO getLine
  return $ CoolString (length s) s

coolOutString :: [CoolValue] -> EvalM CoolValue
coolOutString [CoolString _ s] = do
  st <- get
  liftIO $ putStrLn s
  return $ so st
coolOutString _ = error "Internal: out_string called with bad arguments"

coolInInt :: EvalM CoolValue
coolInInt = do
  s <- liftIO getLine
  let s' = takeWhile (\c -> isSpace c || isDigit c || c == '-') s
  let s'' = dropWhile (\c -> c == '-' || isSpace c) s'
  return $ CoolInt (read s'')

coolOutInt :: [CoolValue] -> EvalM CoolValue
coolOutInt [CoolInt i] = do
  st <- get
  liftIO . putStrLn $ show i
  return $ so st
coolOutInt _ = error "Internal: out_int called with bad arguments"

-- Method dispatch.
-- o is the object to call the method on
-- t is the type of the object
-- m is the method name
-- ps is a list of parameters
-- We handle built-in functions as special cases
dispatch :: Int -> CoolValue -> String -> Identifier -> [CoolValue] -> EvalM CoolValue
dispatch l o t m ps = case (t, idName m) of
    ("String", "length") -> coolLength o
    ("String", "substr") -> coolSubstr l o ps
    ("String", "concat") -> coolConcat o ps
    ("Object", "abort") -> coolAbort ps
    ("Object", "type_name") -> coolTypeName o
    ("Object", "copy") -> coolCopy o
    ("IO", "in_string") -> coolInString
    ("IO", "out_string") -> coolOutString ps
    ("IO", "in_int") -> coolInInt
    ("IO", "out_int") -> coolOutInt ps
    _ -> do
      r <- ask
      case Map.lookup (t, idName m) (implMap r) of
        Nothing -> error "Internal: dispatch on unknown method"
        Just (fs, body) -> do
          st <- get
          let oldEnv = env st
          let oldSO = so st
          zipWithM_ bindVar fs ps
          put st { so = o }
          res <- evalExpr body
          put st { so = oldSO, env = oldEnv }
          return res

objectClass :: CoolValue -> String
objectClass Void = error "Internal: objectClass called on void"
objectClass (CoolInt _) = "Int"
objectClass (CoolBool _) = "Bool"
objectClass (CoolString _ _) = "String"
objectClass (CoolObject _ t _) = t

findClosestAncestor :: ParentMap -> String -> [Formal] -> Maybe Formal
findClosestAncestor pm name bs =
  let l = filter ((== name) . idName . formalName) bs in
  case l of
    [] -> if name == "Object"
          then Nothing
          else case Map.lookup name pm of
            Nothing -> error "Internal: parent map incomplete"
            Just n -> findClosestAncestor pm n bs
    h : _ -> Just h

evalCase :: CoolValue -> Int -> [(Formal, TypeExpr)] -> EvalM CoolValue
evalCase v line bs = case v of
    Void -> throwError ("Runtime: " ++ show line ++ " case on void")
    _ -> do
      r <- ask
      let pm = parentMap r
      case findClosestAncestor pm (objectClass v) (map fst bs) of
        Nothing -> throwError ("Runtime: " ++ show line ++ ": no matching " ++
                               "branch in case expression")
        Just ca -> case lookup ca bs of
          Nothing -> error "Internal: case branch def not found"
          Just e -> do
            st <- get
            let oldEnv = env st
            bindVar (idName $ formalName ca) v
            res <- evalExpr e
            put st { env = oldEnv }
            return res

-- This is the main evaluation function for the interpreter. A Cool program is
-- run by evaluating
-- >>> evalExpr $ DynamicDispatch (New "Main") "main" []
evalExpr :: TypeExpr -> EvalM CoolValue
evalExpr expr@(AnnFix (TypeAnn line typ, e)) = case e of
  Let bs body -> do
    st <- get
    let oldEnv = env st
    mapM_ (\(f, me) -> case me of
                         Just e -> evalExpr e >>= bindVar (idName $ formalName f)
                         Nothing -> bindVar (idName $ formalName f)
                                            (defaultValue $ idName $ formalType f))
          bs
    ret <- evalExpr body
    st2 <- get
    put st2 { env = oldEnv }  -- Get rid of let variables
    return ret
  Case body bs -> do
    ev <- evalExpr body
    evalCase ev line bs
  Assign id e -> do
    st <- get
    ret <- evalExpr e
    bindVar (idName id) ret
    return ret
  DynamicDispatch e m ps -> do
    ev <- evalExpr e
    psv <- mapM evalExpr ps
    case ev of
      CoolInt _ -> dispatch line ev "Int" m psv
      CoolString _ _ -> dispatch line ev "String" m psv
      CoolBool _ -> dispatch line ev "Bool" m psv
      CoolObject _ t _ -> dispatch line ev t m psv
      Void -> throwError ("Runtime: " ++ show line ++ ": dispatch on void")
  StaticDispatch e m t ps -> do
    ev <- evalExpr e
    psv <- mapM evalExpr ps
    dispatch line ev (idName t) m psv
  SelfDispatch m ps -> do
    psv <- mapM evalExpr ps
    st <- get
    let ev = so st
    case ev of
      CoolInt _ -> dispatch line ev "Int" m psv
      CoolString _ _ -> dispatch line ev "String" m psv
      CoolBool _ -> dispatch line ev "Bool" m psv
      CoolObject _ t _ -> dispatch line ev t m psv
      Void -> throwError ("Runtime: " ++ show line ++ ": dispatch on void")
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
  Block es -> foldM (const evalExpr) Void es
  New id -> do
    st <- get
    let t = if idName id == "SELF_TYPE"
            then case so st of
              CoolObject _ t' _ -> t'
              _ -> error "self object is not an object"
            else idName id
    -- We need to have an id, a type name, and map from names to CoolAddresses,
    -- and we need to update the heap with the appropriate values
    r <- ask
    case Map.lookup t (classMap r) of
      Nothing -> error "Internal: class map lookup failed"
      Just init -> undefined
  Isvoid e -> isvoidPure <$> evalExpr e
  Plus x y -> arithOpPure (+) <$> evalExpr x <*> evalExpr y
  Minus x y -> arithOpPure (-) <$> evalExpr x <*> evalExpr y
  Times x y -> arithOpPure (*) <$> evalExpr x <*> evalExpr y
  Divide x y -> do
    ex <- evalExpr x
    ey <- evalExpr y
    if ey == CoolInt 0
    then throwError ("Runtime: " ++ show line ++ ": Division by zero")
    else return $ arithOpPure div ex ey
  Le x y -> compareOpPure (<=) <$> evalExpr x <*> evalExpr y
  Lt x y -> compareOpPure (<) <$> evalExpr x <*> evalExpr y
  Eq x y -> coolEq <$> evalExpr x <*> evalExpr y
  Not e -> notPure <$> evalExpr e
  Negate e -> negatePure <$> evalExpr e
  IntConst i -> return $ CoolInt i
  StringConst s -> return $ CoolString (length s) s
  Id id -> do
    st <- get
    case Map.lookup (idName id) (env st) of
      Nothing  -> if idName id == "self"
                  then return $ so st
                  else error "Internal: Lookup indefined var"
      Just loc -> case Map.lookup loc (store st) of
        Nothing  -> error "Internal error: Problem with ID lookup (store)"
        Just val -> return val
  BoolConst b -> return $ CoolBool b
  Internal -> error ("Internal: shouldn't be evaluating an 'Internal' " ++
                     "expression explicitly")

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
