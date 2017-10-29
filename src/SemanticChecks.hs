{-
Perform a number of semantic checks which can be done before typechecking.
See the list `semanticChecks` toward the bottom of this file for a list of
the checks performed by this module.
-}

module SemanticChecks (performSemanticChecks, getLineage) where

import Data.Tree
import Data.Maybe
import Data.List
import Data.Ord
import Control.Monad

import Types

--import Debug.Trace

-- Builds a tree representing the class heierarchy, e.g. if I have just Main
-- which inherits from IO, I would have
-- Object -> [Bool -> [], Int -> [], String -> [], IO -> [Main -> []]]
classTree :: PosAST -> Either String (Tree String)
classTree (AST cs) = do
  t <- classTree' "Object" ["Object"]
  if length (flatten t) == length cs
     then Right t
     else Left "Error: Cycle in class heierarchy"
 where
  classTree' n l =
    filterM (filterFun n l) cs >>= mapM (mapFun l) >>= Right . Node n
  filterFun n l (Class (Identifier _ name) inherits _) = case inherits of
    Nothing               -> Right False
    Just (Identifier _ i) -> Right (i == n)
  mapFun l (Class (Identifier _ nm) _ _) = classTree' nm (nm : l)

type Exception = (Int, String)

-- Given a class name and the class tree, find all of the ancestors of the class
getLineage :: String -> Tree String -> [String]
getLineage s ct = getLineage' s ct [] where
  getLineage' s (Node n ch) l
    | s == n = l
    | null ch = []
    | otherwise =  foldl' (\acc c -> let l' = getLineage' s c (n : l) in
                                         if null l' then acc else l') [] ch

-- Check to see if any classes are defined twice. Note that the class list
-- should already be sorted at this point.
checkRepeatClasses :: PosAST -> Tree String -> [Exception]
checkRepeatClasses (AST cs) t = case cs of
  []          -> []
  [a]         -> []
  (a : b : l) ->
    if className a == className b
       then (classLine a, "Class " ++ className a ++ " is defined twice") :
              checkRepeatClasses (AST (b : l)) t
       else checkRepeatClasses (AST (b : l)) t

-- It is illegal to define a class called SELF_TYPE
checkRedefinedSelftype :: PosAST -> Tree String -> [Exception]
checkRedefinedSelftype (AST cs) t = mapMaybe fun cs where
  fun c = if className c == "SELF_TYPE"
             then Just (classLine c, "Class is called SELF_TYPE")
             else Nothing

-- Determine whether any classes inherit from String, Int, or Bool
checkIllegalInheritance :: PosAST -> Tree String -> [Exception]
checkIllegalInheritance (AST cs) _ = mapMaybe fun cs where
  fun (Class (Identifier l n) (Just (Identifier _ i)) _) =
    if i == "String" || i == "Int" || i == "Bool"
       then Just (l, "Class " ++ n ++ " inherits from " ++ i)
       else Nothing
  fun _ = Nothing

-- Ensure that every class's parent exists
checkUndefinedInheritance :: PosAST -> [Exception]
checkUndefinedInheritance (AST cs) =
  mapMaybe (fun $ map className cs) cs
 where
   fun cns (Class (Identifier l n) (Just (Identifier _ i)) _) =
     if i `elem` cns then Nothing
                     else Just (l, "Class " ++ n ++ " inherits from undefined"
                                   ++ " class " ++ i)
   fun _ _ = Nothing

-- Look for methods which have return type which are undefined
checkUndefinedReturn :: PosAST -> Tree String -> [Exception]
checkUndefinedReturn (AST cs) _ = let cns = map className cs in
  catMaybes $ concatMap (\c -> map (fun (className c) cns) $
                                  classFeatures c) cs
 where
   fun cn cns (Method (Identifier l n) _ (Identifier _ t) _) =
     if t `elem` cns || t == "SELF_TYPE"
        then Nothing
        else Just (l, "Method " ++ n ++ " of class " ++ cn ++
                      " returns undefined type " ++ t)
   fun _ _ _ = Nothing

-- Look for two attributes or two methods with the same name in one class
checkDuplicateFeatures :: PosAST -> Tree String -> [Exception]
checkDuplicateFeatures (AST cs) _ = concatMap fun cs where
  fun c = let mns = mapMaybe methodName $ classFeatures c
              ans = mapMaybe attrName $ classFeatures c in
          mapMaybe (fun' mns ans c) (classFeatures c)
  methodName (Method (Identifier _ n) _ _ _) = Just n
  methodName _ = Nothing
  attrName (Attribute (Formal (Identifier _ n) _) _) = Just n
  attrName _ = Nothing
  fun' mns ans c (Method (Identifier l n) _ _ _) =
    if length (filter (== n) mns) > 1
       then Just (l, "Method " ++ n ++ " defined twice in class " ++ className c)
       else Nothing
  fun' mns ans c (Attribute (Formal (Identifier l n) _) _) =
    if length (filter (== n) ans) > 1
       then Just (l, "Attribute " ++ n ++ " defined twice in class " ++
                     className c)
       else Nothing

-- Look for a method with two parameters which have the same name
checkDuplicateFormals :: PosAST -> Tree String -> [Exception]
checkDuplicateFormals (AST cs) _ = concatMap fun cs where
  fun c = mapMaybe (fun' c) (classFeatures c)
  fun' c (Method (Identifier _ n) fs _ _) =
    let names = sort $ map (\f -> (idName $ formalName f,
                                   idLine $ formalName f)) fs in
    (\(s, l) -> (l, "Two parameters called " ++ s ++ " found in method " ++
                         n ++ " of class " ++ className c)) <$> findDuplicate names
  fun' c _ = Nothing
  findDuplicate []       = Nothing
  findDuplicate [_]      = Nothing
  findDuplicate ((s1, l1) : b@(s2, _) : as) =
    if s1 == s2 then Just (s1, l1) else findDuplicate (b : as)

-- Look for an attribute or formal called self
checkAttributeOrFormalSelf :: PosAST -> Tree String -> [Exception]
checkAttributeOrFormalSelf (AST cs) _ = concatMap fun cs where
  fun c = concatMap (fun' c) (classFeatures c)
  fun' c (Method (Identifier _ n) fs _ _) = mapMaybe (fun'' c n) fs
  fun' c (Attribute (Formal (Identifier l n) _) _) =
    [(l, "self is used as an attribute in class " ++ className c) | n == "self"]
  fun'' c n (Formal (Identifier l n') _) =
    if n' == "self"
       then Just (l, "self is used as a parameter in method " ++ n ++
                     " in class " ++ className c)
       else Nothing

-- Look for a parameter with the type SELF_TYPE
checkSelftypeFormal :: PosAST -> Tree String -> [Exception]
checkSelftypeFormal (AST cs) _ = concatMap fun cs where
  fun c = concatMap (fun' c) (classFeatures c)
  fun' c (Method (Identifier _ n) fs _ _) = mapMaybe (fun'' c n) fs
  fun' c _ = []
  fun'' c n (Formal (Identifier _ n') (Identifier l t)) =
    if t == "SELF_TYPE"
       then Just (l, "Parameter " ++ n' ++ " of method " ++ n ++ " in class " ++
                     className c ++ " has type SELF_TYPE")
       else Nothing

checkRedefinedMethods :: PosAST -> Tree String -> [Exception]
checkRedefinedMethods (AST cs) ct = concatMap fun cs where
  fun c = let lineage = getLineage (className c) ct
              classes = filter (\c' -> className c' `elem` lineage) cs
              methods = concatMap (mapMaybe nameMethod . classFeatures)
                                  classes in
          mapMaybe (fun' methods c) (classFeatures c)
  nameMethod m@(Method (Identifier _ n) _ _ _) = Just (n, m)
  nameMethod _ = Nothing
  fun' ms c (Method n@(Identifier l s) ps t _) = case lookup s ms of
    Nothing -> Nothing
    Just (Method n' ps' t' _) ->
      if n == n' && ps == ps' && t == t'
         then Nothing
         else Just (l, "Method " ++ s ++ " overridden in class " ++
                       className c ++ " but given different signature")
  fun' _ _ _ = Nothing

-- Look for attributes that are overridden from a parent class
checkRedefinedAttrs :: PosAST -> Tree String -> [Exception]
checkRedefinedAttrs (AST cs) ct = concatMap fun cs where
  fun c = let lineage = getLineage (className c) ct
              classes = filter (\c' -> className c' `elem` lineage) cs
              ans = concatMap (mapMaybe attrName . classFeatures)
                              classes in
          mapMaybe (fun' ans c) (classFeatures c)
  attrName (Attribute (Formal (Identifier _ n) _) _) = Just n
  attrName _ = Nothing
  fun' ans c (Attribute (Formal (Identifier l n) _) _) =
    if n `elem` ans
       then Just (l, "Attribute " ++ n ++ " redefined in class " ++ className c)
       else Nothing
  fun' _ _ _ = Nothing

-- Make sure there is a class called Main which defines a method called main
-- which takes zero arguments
checkMissingMain :: PosAST -> Tree String -> [Exception]
checkMissingMain (AST cs) _ = case filter ((== "Main") . className) cs of
  []      -> [(0, "Class Main not defined")]
  (c : _) -> case filter fun $ classFeatures c of
    [] -> [(classLine c, "Method main not defined in class Main")]
    (Method _ fs _ _ : _) ->
      if null fs
         then []
         else [(classLine c, "Method main in class Main takes parameters")]
 where
   fun (Method (Identifier _ n) _ _ _) = n == "main"
   fun _ = False

-- These functions perform a number of semantic checks. The results are a list
-- of errors found, where each pair (l, err) consists of the line number and
-- nature of the error
-- The arguments are the AST and the class heierarchy
semanticChecks :: [PosAST -> Tree String -> [Exception]]
semanticChecks = [ checkRepeatClasses
                 , checkRedefinedSelftype
                 , checkIllegalInheritance
                 , checkUndefinedReturn
                 , checkDuplicateFeatures
                 , checkDuplicateFormals
                 , checkAttributeOrFormalSelf
                 , checkSelftypeFormal
                 , checkRedefinedMethods
                 , checkRedefinedAttrs
                 , checkMissingMain ]

-- Perform all of the above semantic checks. We treat checkUndefinedInheritance
-- as a special case because it needs to come before we check the class
-- heierarchy for cycles (otherwise the analyzer thinks a cycle has occured
-- whenever anything inherits from an undefined class). The Right constructor
-- is used for the class tree if an error is not found
performSemanticChecks :: PosAST -> Either String (Tree String)
performSemanticChecks ast@(AST cs) =
  case checkUndefinedInheritance ast of
    [] ->
      case classTree ast of
        Left err -> Left err
        Right ct ->
          let ast' = AST $ sortBy classOrder cs in
          case concatMap (\f -> f ast' ct) semanticChecks of
            []   -> Right ct
            errs -> Left $ intercalate "\n" $
                           map (\(l, e) -> "Error on line " ++ show l ++ ": " ++
                                           e) errs
    errs -> Left $ intercalate "\n" $ map (\(l, e) -> "Error on line " ++
                                                      show l ++ ": " ++ e) errs
 where
   classOrder (Class (Identifier _ a) _ _) (Class (Identifier _ b) _ _)
     | a < b = LT
     | a == b = EQ
     | otherwise = GT
