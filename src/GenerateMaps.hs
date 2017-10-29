{-
This module generates the class map, parent map, and implementation map for a
Cool program. This is separated from the interpreter and the code generator
because it is needed by both.
-}

module GenerateMaps ( classMap
                    , parentMap
                    , implMap
                    ) where

import Data.List
import Data.Tree
import qualified Data.Map.Strict as Map

import Types

-- The parent map stores the parent of each class. For case statements it is
-- easier to have this stored in a single map rather than going through each
-- class and pattern matching to look for parents
parentMap :: TypeAST -> ParentMap
parentMap (AST cs) = foldl' foldFun Map.empty cs where
  foldFun acc (Class _  Nothing  _) = acc
  foldFun acc (Class id (Just p) _) = Map.insert (idName id) (idName p) acc

-- Given a class, get a list of all of its attributes including inherited ones
getAttrs :: TypeAST -> TypeClass -> [(String, (String, Maybe TypeExpr))]
getAttrs ast@(AST cs) (Class id pc as) = case pc of
  Nothing -> map getAttr $ filter isAttr as
  Just p  -> getAttrs ast (getClassByName cs $ idName p) ++
               map getAttr (filter isAttr as)
 where
   isAttr Method {} = False
   isAttr Attribute {} = True
   getAttr (Attribute (Formal n t) e) = (idName n, (idName t, e))

-- The class map stores the attributes of each class. Attributes are stored as
-- an association list where attribute name is associated to
-- (type, Maybe initializer)
classMap :: TypeAST -> ClassMap
classMap ast@(AST cs) = foldl' foldFun Map.empty cs where
  foldFun acc c@(Class id _ as) = Map.insert (idName id) (getAttrs ast c) acc

-- Finds the methods for a single class and all of its ancestors, prefering the
-- most specific given definition
getMethods :: String -> TypeAST -> TypeClass -> ImplMap
getMethods s ast@(AST cs) (Class _ cp fs) = case cp of
  Nothing -> foldl' foldFun Map.empty $ filter isMethod fs
  Just p  -> Map.union (foldl' foldFun Map.empty $ filter isMethod fs)
                       (getMethods s ast (getClassByName cs $ idName p))
 where
   isMethod Method {} = True
   isMethod Attribute {} = False
   foldFun acc (Method mn ps t b) = Map.insert (s, idName mn)
                                               (map (idName . formalName) ps, b)
                                               acc

-- The implementation map stores the definition of methods. This is a map from
-- (class_name, method_name) to ([args], method_body)
implMap :: TypeAST -> ImplMap
implMap ast@(AST cs) = foldl' foldFun Map.empty cs where
  foldFun acc c = Map.union acc (getMethods (className c) ast c)
