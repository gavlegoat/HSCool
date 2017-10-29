{-
Defines any types which are needed in several parts of the program. Types local
to a single module are defined in the appropriate module. Also contains a few
utilities which are needed by several modules.
-}

{-# LANGUAGE FlexibleInstances #-}

module Types where

import Data.Int
import Control.Arrow ((&&&))
import qualified Data.Map.Strict as Map

data TypeAnn = TypeAnn { typeLine :: Int, typeName :: String }

instance Show TypeAnn where
  show (TypeAnn l n) = show l ++ "\n" ++ n

data Identifier = Identifier { idLine :: Int, idName :: String }

instance Show Identifier where
  show (Identifier line name) = show line ++ "\n" ++ name ++ "\n"

instance Eq Identifier where
  a == b = idName a == idName b

data Formal = Formal { formalName :: Identifier, formalType ::  Identifier }

instance Show Formal where
  show (Formal name typ) = show name ++ show typ

instance Eq Formal where
  a == b = (formalName a == formalName b) && (formalType a == formalType b)

{- Since I haven't done fixed point functor stuff before I'm going to try to
 - give some kind of explanation of this. It's based on the material at
 - http://martijn.van.steenbergen.nl/journal/2010/06/24/generically-adding-position-information-to-a-datatype/
 -
 - Basically, with ExprF, what we do is turn a recursive datatype into a non-
 - recursive one by adding a type parameter a which stands in for the recursion.
 - The Fix functor (defined as Fix f = In { out :: f (Fix f) }) can be used
 - to allow recursion as normal. In this case this is important because we use
 - this ability to avoid explicit recursion to allow arbitrary annotations to
 - be attached to expressions.
 -}

data ExprF a =
    Let [(Formal, Maybe a)] a
  | Case a [(Formal, a)]
  | Assign Identifier a
  | DynamicDispatch a Identifier [a]
  | StaticDispatch a Identifier Identifier [a]
  | SelfDispatch Identifier [a]
  | If a a a
  | While a a
  | Block [a]
  | New Identifier
  | Isvoid a
  | Plus a a
  | Minus a a
  | Times a a
  | Divide a a
  | Lt a a
  | Le a a
  | Eq a a
  | Not a
  | Negate a
  | IntConst Int32
  | StringConst String
  | Id Identifier
  | BoolConst Bool
  | Internal

sndMap :: (b -> c) -> [(a, b)] -> [(a, c)]
sndMap f = map (fst &&& (f . snd))

instance Functor ExprF where
  fmap f (Let bs b)                 = Let (sndMap (fmap f) bs) (f b)
  fmap f (Case b bs)                = Case (f b) (sndMap f bs)
  fmap f (Assign id e)              = Assign id (f e)
  fmap f (DynamicDispatch e id es)  = DynamicDispatch (f e) id (map f es)
  fmap f (StaticDispatch e t id es) = StaticDispatch (f e) t id (map f es)
  fmap f (SelfDispatch id es)       = SelfDispatch id (map f es)
  fmap f (If p t e)                 = If (f p) (f t) (f e)
  fmap f (While p b)                = While (f p) (f b)
  fmap f (Block es)                 = Block (map f es)
  fmap _ (New id)                   = New id
  fmap f (Isvoid e)                 = Isvoid (f e)
  fmap f (Plus x y)                 = Plus (f x) (f y)
  fmap f (Minus x y)                = Minus (f x) (f y)
  fmap f (Times x y)                = Times (f x) (f y)
  fmap f (Divide x y)               = Divide (f x) (f y)
  fmap f (Le x y)                   = Le (f x) (f y)
  fmap f (Lt x y)                   = Lt (f x) (f y)
  fmap f (Eq x y)                   = Eq (f x) (f y)
  fmap f (Not e)                    = Not (f e)
  fmap f (Negate e)                 = Negate (f e)
  fmap _ (IntConst i)               = IntConst i
  fmap _ (StringConst i)            = StringConst i
  fmap _ (BoolConst i)              = BoolConst i
  fmap _ (Id id)                    = Id id
  fmap _ Internal                   = Internal

-- Associate arbitrary data at each recursive call.
newtype AnnFix x f = AnnFix { runAnnFix :: (x, f (AnnFix x f)) }

instance (Show a) => Show (AnnFix a ExprF) where
  show (AnnFix (x, expr)) = show x ++ "\n" ++ case expr of
    Let bs body -> "let\n" ++ printList' showLetBinding bs ++ show body
    Case body bs -> "case\n" ++ show body ++ printList' showCaseBranch bs
    Assign id e -> "assign\n" ++ show id ++ show e
    DynamicDispatch e m ps ->
      "dynamic_dispatch\n" ++ show e ++ show m ++ printList ps
    StaticDispatch e m t ps ->
      "static_dispatch\n" ++ show e ++ show m ++ show t ++ printList ps
    SelfDispatch m ps -> "self_dispatch\n" ++ show m ++ printList ps
    If p t f -> "if\n" ++ show p ++ show t ++ show f
    While p b -> "while\n" ++ show p ++ show b
    Block es -> "block\n" ++ printList es
    New id -> "new\n" ++ show id
    Isvoid e -> "isvoid\n" ++ show e
    Plus x y -> "plus\n" ++ show x ++ show y
    Minus x y -> "minus\n" ++ show x ++ show y
    Times x y -> "times\n" ++ show x ++ show y
    Divide x y -> "divide\n" ++ show x ++ show y
    Le x y -> "le\n" ++ show x ++ show y
    Lt x y -> "lt\n" ++ show x ++ show y
    Eq x y -> "eq\n" ++ show x ++ show y
    Not e -> "not\n" ++ show e
    Negate e -> "negate\n" ++ show e
    IntConst i -> "integer\n" ++ show i ++ "\n"
    StringConst s -> "string\n" ++ s ++ "\n"
    Id id -> "identifier\n" ++ show id
    BoolConst True -> "true\n"
    BoolConst False -> "false\n"
    Internal -> "internal\n"

-- This type allows us to annotate each expression with the line number it is on
type PosExpr = AnnFix Int ExprF

-- The TypeExpr type is for expressions which have associated line numbers and
-- types
type TypeExpr = AnnFix TypeAnn ExprF

exprType :: TypeExpr -> String
exprType (AnnFix (TypeAnn _ t, _)) = t

data Feature a =
    Attribute Formal (Maybe (AnnFix a ExprF))
  | Method Identifier [Formal] Identifier (AnnFix a ExprF)  -- name, formals, type, body

instance (Show a) => Show (Feature a) where
  show (Method name params typ body) =
    "method\n" ++ show name ++ printList params ++ show typ ++ show body
  show (Attribute attr init) = case init of
    Just expr -> "attribute_init\n" ++ show attr ++ show expr
    Nothing   -> "attribute_no_init\n" ++ show attr

type PosFeature = Feature Int
type TypeFeature = Feature TypeAnn

data Class a = Class Identifier (Maybe Identifier) [Feature a]

className :: Class a -> String
className (Class (Identifier _ n) _ _) = n

classLine :: Class a -> Int
classLine (Class (Identifier l _) _ _) = l

classFeatures :: Class a -> [Feature a]
classFeatures (Class _ _ fs) = fs

instance (Show a) => Show (Class a) where
  show (Class name inherits features) = case inherits of
    Just i  -> show name ++ "inherits\n" ++ show i ++ printList features
    Nothing -> show name ++ "no_inherits\n" ++ printList features

type PosClass = Class Int
type TypeClass = Class TypeAnn

newtype AST a = AST [Class a]

instance (Show a) => Show (AST a) where
  show (AST cs) = printList cs

type PosAST = AST Int
type TypeAST = AST TypeAnn

-- Given a class name, find the class associated with it. This function is only
-- used internally to construct the method store so we should never find two
-- classes with the same name or fail to find a matching class
getClassByName :: [Class a] -> String -> Class a
getClassByName cs c = case filter (\cl -> className cl == c) cs of
  []  -> error "Internal error: getClassByName: no matching class found"
  [x] -> x
  _   -> error "Internal error: getClassByName: Two classes with the same name"

printList :: (Show a) => [a] -> String
printList = printList' show

printList' :: (a -> String) -> [a] -> String
printList' f l = show (length l) ++ "\n" ++ concatMap f l

showLetBinding :: (Show a) => (Formal, Maybe (AnnFix a ExprF)) -> String
showLetBinding (f, i) = case i of
  Nothing -> "let_binding_no_init\n" ++ show f
  Just e  -> "let_binding_init\n" ++ show f ++ show e

showCaseBranch :: (Show a) => (Formal, AnnFix a ExprF) -> String
showCaseBranch (f, c) = show f ++ show c

-- Maps a class name to a list of attribute names and initializers. The value
-- for each class is an association list mapping attribute name to type (which
-- is necessary for default initializiations) and an optional inititialization
-- expression. We keep the internal attribute mapping as an association list
-- rather than a map because we need to preserve ordering to initializ properly
type ClassMap = Map.Map String [(String, (String, Maybe TypeExpr))]

-- The parent map is a mapping from each class name to the parent of that class.
-- In some sense it is an inverted form of the class tree used by the
-- typechecker.
type ParentMap = Map.Map String String

-- Maps a method name to its formal list and implementation
type ImplMap = Map.Map (String, String) ([String], TypeExpr)
