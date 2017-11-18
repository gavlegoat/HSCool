{-
Typecheck the AST after it has passed semantic checks. In the process the
PosAST (annotated with just line numbers) is converted to a TypeAST (annotated
with both line numbers and types).
-}

module Typecheck (annotateAST) where

import Data.Either
import Data.List
import Data.Tree
import Data.Maybe
import Control.Monad
import qualified Data.Map.Strict as Map

import Types
import SemanticChecks

-- The method store is a map of (method_name, class_name) -> types where
-- types is the return type followed by the types of each formal
type MethodStore = Map.Map (String, String) [String]

-- The environment is a map of var_name -> type
type Environment = Map.Map String String

-- Given a list of either errors or values, we want to give back either a list
-- of values (if there were no errors) or a new error which is the concatenation
-- of all of the input errors
collectErrors :: [Either [(Int, String)] a] -> Either [(Int, String)] [a]
collectErrors es = case lefts es of
  []   -> sequence es
  errs -> Left $ concat errs

-- Combine a number of error messages into a single string for printing
showErrors :: Either [(Int, String)] a -> Either String a
showErrors (Right x) = Right x
showErrors (Left es) = Left $ intercalate "\n" $ map showErr (sort es) where
  showErr (l, e) = "Error on line " ++ show l ++ ": " ++ e

-- Build the method store
methodStore :: AST a -> Tree String -> MethodStore
methodStore (AST cs) ct = foldl' oneLineage Map.empty (map className cs) where
  oneLineage acc cl = foldl' (\ac c -> oneClass ac cl (getClassByName cs c)) acc
                             (cl : getLineage cl ct)
  oneClass ac cn c = foldl' (\a f -> case f of
                               Method (Identifier _ n) fs (Identifier _ t) _ ->
                                 Map.insert (n, cn)
                                            (t : map (idName . formalType) fs)
                                            a
                               _ -> a) ac (classFeatures c)

-- Create the type environment for a given class, including all of its declared
-- and inherited attributes
typeEnv :: AST a -> Class a -> Tree String -> Environment
typeEnv (AST cs) cl ct = let l = getLineage (className cl) ct in
  foldl' (\acc c ->
            if className c == className cl || className c `elem` l
               then foldl' (\a f -> case f of
                              Method {} -> a
                              Attribute f _ ->
                                Map.insert (idName (formalName f))
                                           (idName (formalType f)) a)
                           acc $ classFeatures c
               else acc) Map.empty cs

-- Add the formal parameters of a method to an environment
addEnvFormals :: Environment -> [Formal] -> Environment
addEnvFormals = foldl' (\a (Formal (Identifier _ n) (Identifier _ t)) ->
                          Map.insert n t a)

-- Determine whether a is a subtype of b
isSubtype :: Tree String -> String -> String -> Bool
isSubtype ct a b = a == b || b `elem` getLineage a ct

-- Since the type annotation cases for +, -, *, and / are almost identical, they
-- are all handled with this function
arithmeticBinOps :: Int -> (TypeExpr -> TypeExpr -> ExprF TypeExpr) ->
                    Either [(Int, String)] TypeExpr ->
                    Either [(Int, String)] TypeExpr ->
                    Either [(Int, String)] TypeExpr
arithmeticBinOps l cons e1 e2 = case (e1, e2) of
 (Left errs1, Left errs2) -> Left $ errs1 ++ errs2
 (Left errs1, Right e2') ->
   if typeName (fst (runAnnFix e2')) == "Int"
      then Left errs1
      else Left $ (l, "Second argument of arithmetic operator is non-integer") : errs1
 (Right e1', Left errs2) ->
   if typeName (fst (runAnnFix e1')) == "Int"
      then Left errs2
      else Left $ (l, "First argument of arithmetic operator is non-integer") : errs2
 (Right e1', Right e2')
   | typeName (fst (runAnnFix e1')) == "Int" ->
      if typeName (fst (runAnnFix e2')) == "Int"
         then Right $ AnnFix (TypeAnn l "Int", cons e1' e2')
         else Left [(l, "Second argument of arithmetic operator is non-integer")]
   | typeName (fst (runAnnFix e2')) == "Int" ->
      Left [(l, "First argument of arithmetic operator is non-integer")]
   | otherwise -> Left [(l, "First argument of arithmetic operator is non-integer"),
                        (l, "Second argument of arithmetic operator is non-integer")]

-- Determine whether two values can legally be compared
comparisonCheck :: String -> String -> Bool
comparisonCheck a b = not (a == "Int" || b == "Int" || a == "Bool" ||
                          b == "Bool" || a == "String" || b == "String") || a == b

-- Given two types, find the most specific type which is an ancestor of both
-- types. This is guaranteed to exist because all types inherit from Object
leastType :: String -> String -> Tree String -> String
leastType t1 t2 ct = let l1 = t1 : reverse (getLineage t1 ct)
                         l2 = t2 : reverse (getLineage t2 ct) in
                     head . filter (`elem` l2) $ l1

-- As above, but with more than two types
leastTypeMult :: Tree String -> [String] -> String
leastTypeMult _  []             = error "Internal: no arguments to leastTypeMult"
leastTypeMult _  [t]            = t
leastTypeMult ct (t1 : t2 : ts) = leastTypeMult ct (leastType t1 t2 ct : ts)

-- Check to make sure the arguments to a method are correct and return any
-- errors that are found
checkMethodType :: Int -> String -> String -> Environment -> MethodStore ->
                   Tree String -> String -> [PosExpr] ->
                   Either [(Int, String)] (String, [TypeExpr])
checkMethodType l cn mn gamma ms ct so es = case Map.lookup (mn, cn) ms of
  Nothing -> Left [(l, "Method " ++ mn ++ " of class " ++ cn ++ " undefined")]
  Just (rt : ts) ->
    if length ts /= length es
       then Left [(l, "Incorrect number of arguments passed to method " ++ mn)]
       else case collectErrors $ map (annotateExpr gamma ms ct so) es of
              Left errs -> Left errs
              Right es' -> let argTypes = map exprType es' in
                case catMaybes $ zipWith (mapFun l mn) ts argTypes of
                  []   -> Right (rt, es')
                  errs -> Left errs
 where
   mapFun l mn t t' = if isSubtype ct t' t
                         then Nothing
                         else Just (l, "Type mismatch in arguments of method " ++
                                       mn ++ ": Expected " ++ t ++ " got " ++ t')

-- Recursively add a type to a let expression so that each binding is visible in
-- the initializers of later bindings
addLetType :: Environment -> MethodStore -> Tree String -> String ->
              [(Formal, Maybe PosExpr)] -> PosExpr ->
              Either [(Int, String)] TypeExpr
addLetType gamma ms ct so bs e = case bs of
  [] -> case annotateExpr gamma ms ct so e of
    Left errs -> Left errs
    Right e'@(AnnFix (ta, _)) -> Right $ AnnFix (ta, Let [] e')
  ((f, Nothing) : bs') ->
    case addLetType (addEnvFormals gamma [f]) ms ct so bs' e of
      Left errs -> Left errs
      Right (AnnFix (ta, Let xs e')) ->
        Right $ AnnFix (ta, Let ((f, Nothing) : xs) e')
  ((f, Just i) : bs') ->
    let le = addLetType (addEnvFormals gamma [f]) ms ct so bs' e
        ie = annotateExpr gamma ms ct so i in
    case collectErrors [le, ie] of
      Left errs -> Left errs
      Right [e'@(AnnFix (ta, Let xs _)), ie'@(AnnFix (TypeAnn l t, _))] ->
        if t == idName (formalType f)
           then Right $ AnnFix (ta, Let ((f, Just ie') : xs) e')
           else Left [(l, "Initilization expression in let is of the wrong type")]

-- Determine whether a case expression contains two branches with the same type,
-- e.g. case e of x : Int => true; y : Int => false; esac
dupCaseBranches :: ExprF PosExpr -> Bool
dupCaseBranches (Case _ bs) =
  let ts = map (idName . formalType . fst) bs in nub ts /= ts
dupCaseBranches _ = error "Internal: dupCaseBranches called on non-case"

-- Look for self used as an identifier in case expressions
selfInCaseBranch :: ExprF PosExpr -> Bool
selfInCaseBranch (Case _ bs) =
  elem "self" $ map (idName . formalName . fst) bs
selfInCaseBranch _ = error "Internal: selfInCaseBranch called on non-case"

selfTypeCaseBranch :: ExprF PosExpr -> Bool
selfTypeCaseBranch (Case _ bs) =
  elem "SELF_TYPE" $ map (idName . formalType . fst) bs

-- Look for self used as an identifier in let expressions
selfInLetBinding :: ExprF PosExpr -> Bool
selfInLetBinding (Let bs _) =
  elem "self" $ map (idName . formalName . fst) bs
selfInLetBinding _ = error "Internal: selfInLetBinding called on non-let"

-- Add a type annotation to an expression or return a type error.
annotateExpr :: Environment -> MethodStore -> Tree String -> String ->
                PosExpr -> Either [(Int, String)] TypeExpr
annotateExpr gamma ms ct so (AnnFix (l, e)) = case e of
  Let bs b -> if selfInLetBinding e
                 then Left [(l, "self used as an identifer in a let binding")]
                 else addLetType gamma ms ct so bs b
  Case e0 bs
    | dupCaseBranches e ->
        Left [(l, "Two branches of a case statement have the same type")]
    | selfInCaseBranch e -> Left [(l, "self used as a variable in case branch")]
    | selfTypeCaseBranch e ->
        Left [(l, "SELF_TYPE used as the type in a case branch")]
    | otherwise -> case annotateExpr gamma ms ct so e0 of
        Left errs -> Left errs
        Right e@(AnnFix (TypeAnn _ t', _)) ->
          case collectErrors $
               map (\(f, ei) -> annotateExpr (addEnvFormals gamma [f])
                                             ms ct so ei) bs of
            Left errs -> Left errs
            Right es -> Right $ AnnFix (TypeAnn l (leastTypeMult ct $ map exprType es),
                                       Case e $ zip (map fst bs) es)
  Assign id@(Identifier _ n) e1 -> case annotateExpr gamma ms ct so e1 of
    Left errs -> Left errs
    Right e@(AnnFix (TypeAnn _ t', _)) ->
      case Map.lookup n gamma of
        Nothing -> Left [(l, "Assignment to undefined variable " ++ n)]
        Just t -> if isSubtype ct t' t
                     then Right $ AnnFix (TypeAnn l t, Assign id e)
                     else Left [(l, "Ill-typed assignment to variable " ++ n)]
  DynamicDispatch e0 f es -> case annotateExpr gamma ms ct so e0 of
    Left errs -> Left errs
    Right e' ->
      case checkMethodType l (exprType e') (idName f) gamma ms ct so es of
        Left errs       -> Left errs
        Right (rt, es') ->
          if rt == "SELF_TYPE"
             then Right $ AnnFix (TypeAnn l so, DynamicDispatch e' f es')
             else Right $ AnnFix (TypeAnn l rt, DynamicDispatch e' f es')
  StaticDispatch e0 t f es -> case annotateExpr gamma ms ct so e0 of
    Left errs -> Left errs
    Right e' -> if isSubtype ct (exprType e') (idName t)
                   then case checkMethodType l (exprType e') (idName f)
                                             gamma ms ct so es of
                          Left errs -> Left errs
                          Right (rt, es') ->
                            if rt == "SELF_TYPE"
                               then Right $ AnnFix (TypeAnn l so,
                                                    StaticDispatch e' t f es')
                               else Right $ AnnFix (TypeAnn l rt,
                                                    StaticDispatch e' t f es')
                   else Left [(l, "Type mismatch in static dispatch: Expected " ++
                                  idName t ++ " but got " ++ exprType e')]
  SelfDispatch f es -> case checkMethodType l so (idName f) gamma ms ct so es of
    Left errs       -> Left errs
    Right (rt, es') ->
      if rt == "SELF_TYPE"
         then Right $ AnnFix (TypeAnn l so, SelfDispatch f es')
         else Right $ AnnFix (TypeAnn l rt, SelfDispatch f es')
  If e1 e2 e3 ->
    case collectErrors $ map (annotateExpr gamma ms ct so) [e1, e2, e3] of
      Left errs -> Left errs
      Right [e1'@(AnnFix (TypeAnn _ "Bool", _)), e2'@(AnnFix (TypeAnn _ t1, _)),
             e3'@(AnnFix (TypeAnn _ t2, _))] ->
        Right $ AnnFix (TypeAnn l (leastType t1 t2 ct), If e1' e2' e3')
      _ -> Left [(l, "Predicate in if statement is not of type Bool")]
  While e1 e2 -> case collectErrors [annotateExpr gamma ms ct so e1,
                                     annotateExpr gamma ms ct so e2] of
    Left errs -> Left errs
    Right [e1'@(AnnFix (TypeAnn _ "Bool", _)), e2'] ->
      Right $ AnnFix (TypeAnn l "Object", While e1' e2')
    _ -> Left[(l, "Predicate in while loop is not of type Bool")]
  Block es -> case collectErrors $ map (annotateExpr gamma ms ct so) es of
    Left errs -> Left errs
    Right es  -> let (AnnFix (TypeAnn _ t, _)) = last es in
                 Right $ AnnFix (TypeAnn l t, Block es)
  New t -> let t' = if idName t == "SELF_TYPE" then so else idName t in
    Right $ AnnFix (TypeAnn l t', New t)
  Isvoid e1 -> (\x -> AnnFix (TypeAnn l "Bool", Isvoid x)) <$>
               annotateExpr gamma ms ct so e1
  Plus e1 e2 -> arithmeticBinOps l Plus (annotateExpr gamma ms ct so e1)
                                 (annotateExpr gamma ms ct so e2)
  Minus e1 e2 -> arithmeticBinOps l Minus (annotateExpr gamma ms ct so e1)
                                  (annotateExpr gamma ms ct so e2)
  Times e1 e2 -> arithmeticBinOps l Times (annotateExpr gamma ms ct so e1)
                                  (annotateExpr gamma ms ct so e2)
  Divide e1 e2 -> arithmeticBinOps l Times (annotateExpr gamma ms ct so e1)
                                   (annotateExpr gamma ms ct so e2)
  Lt e1 e2 -> case collectErrors [annotateExpr gamma ms ct so e1,
                                  annotateExpr gamma ms ct so e2] of
    Left errs -> Left errs
    Right [e1'@(AnnFix (TypeAnn _ t1, _)), e2'@(AnnFix (TypeAnn _ t2, _))] ->
      if t1 `elem` ["Int", "String", "Bool"]
         then if t1 == t2
                 then Right $ AnnFix (TypeAnn l "Bool", Lt e1' e2')
                 else Left [(l, "Comparison on non-matching basic classes")]
         else Right $ AnnFix (TypeAnn l "Bool", Lt e1' e2')
  Le e1 e2 -> case collectErrors [annotateExpr gamma ms ct so e1,
                                  annotateExpr gamma ms ct so e2] of
    Left errs -> Left errs
    Right [e1'@(AnnFix (TypeAnn _ t1, _)), e2'@(AnnFix (TypeAnn _ t2, _))] ->
      if t1 `elem` ["Int", "String", "Bool"]
         then if t1 == t2
                 then Right $ AnnFix (TypeAnn l "Bool", Le e1' e2')
                 else Left [(l, "Comparison on non-matching basic classes")]
         else Right $ AnnFix (TypeAnn l "Bool", Le e1' e2')
  Eq e1 e2 -> case collectErrors [annotateExpr gamma ms ct so e1,
                                  annotateExpr gamma ms ct so e2] of
    Left errs -> Left errs
    Right [e1'@(AnnFix (TypeAnn _ t1, _)), e2'@(AnnFix (TypeAnn _ t2, _))] ->
      if t1 `elem` ["Int", "String", "Bool"]
         then if t1 == t2
                 then Right $ AnnFix (TypeAnn l "Bool", Eq e1' e2')
                 else Left [(l, "Comparison on non-matching basic classes")]
         else Right $ AnnFix (TypeAnn l "Bool", Eq e1' e2')
  Not e1 -> annotateExpr gamma ms ct so e1 >>= \e' ->
    if typeName (fst (runAnnFix e')) == "Bool"
       then Right $ AnnFix (TypeAnn l "Bool", Not e')
       else Left [(l, "Not applied to non-boolean")]
  Negate e1 -> annotateExpr gamma ms ct so e1 >>= \e' ->
    if typeName (fst (runAnnFix e')) == "Int"
       then Right $ AnnFix (TypeAnn l "Int", Negate e')
       else Left [(l, "Negate applied to non-integer")]
  IntConst i -> Right $ AnnFix (TypeAnn l "Int", IntConst i)
  StringConst s -> Right $ AnnFix (TypeAnn l "String", StringConst s)
  Id id -> case Map.lookup (idName id) gamma of
    Just t  -> if t == "SELF_TYPE"
                  then Right $ AnnFix (TypeAnn l so, Id id)
                  else Right $ AnnFix (TypeAnn l t, Id id)
    Nothing -> if idName id == "self"
                  then Right $ AnnFix (TypeAnn l so, Id id)
                  else Left [(l, "Undefined identifier: " ++ idName id)]
  BoolConst b -> Right $ AnnFix (TypeAnn l "Bool", BoolConst b)
  Internal _ -> error "Internal: shouldn't be typechecking internals"

-- Add type annotations to any expressions associated with a feature. Return any
-- type errors or check to ensure method and attribute types are consistent with
-- their declarations.
annotateFeature :: MethodStore -> Tree String -> Environment -> String ->
                   PosFeature -> Either [(Int, String)] TypeFeature
annotateFeature ms ct gamma cn (Method n ps t b) =
  annotateExpr (addEnvFormals gamma ps) ms ct cn b >>= \e@(AnnFix (t', _)) ->
    if isSubtype ct (typeName t') (idName t)
       then Right $ Method n ps t e
       else Left [(typeLine t', "Return type of method " ++ idName n ++
                                " in class " ++ cn ++
                                " does not match signature")]
annotateFeature ms ct gamma cn (Attribute f (Just i)) =
  annotateExpr gamma ms ct cn i >>= \e@(AnnFix (t', _)) ->
    if isSubtype ct (typeName t') (idName (formalType f))
       then Right $ Attribute f (Just e)
       else Left [(typeLine t', "Initializer of attribute " ++
                                idName (formalName f) ++ " in class " ++ cn ++
                                " does not match declaration")]
annotateFeature ms ct gamma cn (Attribute f Nothing) =
  Right $ Attribute f Nothing

-- Internal classes don't need typechecking but they do have to have type
-- annotations in order to work with Haskell's typechecker
posToTypeClassInt :: PosClass -> TypeClass
posToTypeClassInt (Class n i fs) = Class n i $ map posToTypeFeatInt fs where
  posToTypeFeatInt (Method n ps t e) = Method n ps t $ p2tE e
  posToTypeFeatInt (Attribute f (Just i)) = Attribute f $ Just $ p2tE i
  p2tE (AnnFix (l, e)) = AnnFix (TypeAnn l "", fmap p2tE e)

-- Add type annotations to all features in a class. Return any type errors
annotateClass :: PosAST -> MethodStore -> Tree String -> PosClass ->
                 Either [(Int, String)] TypeClass
annotateClass ast ms ct c@(Class n@(Identifier l n') i fs) =
  if l == 0 then Right $ posToTypeClassInt c else
  let gamma = typeEnv ast c ct in
  fmap (Class n i) . collectErrors $ map (annotateFeature ms ct gamma n') fs

-- Add type annotations for each class in the program. The result is a syntax
-- tree annotated with type information or a type error.
annotateAST :: PosAST -> Tree String -> Either String TypeAST
annotateAST ast@(AST cs) ct = let ms = methodStore ast ct in
  fmap AST . showErrors . collectErrors $ map (annotateClass ast ms ct) cs
