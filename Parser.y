{
module Parser (parse) where

import Control.Monad.State
import Data.Maybe

import LexParse
import Lexer
import Types
}

%name parserAct
%tokentype {Token}
%error {parseError}
%monad {P}
%lexer {lexer} {Token TokEOF _}

%token

'@'         { Token TokAt _ }
case        { Token TokCase _ }
class       { Token TokClass _ }
':'         { Token TokColon _ }
','         { Token TokComma _ }
'/'         { Token TokDivide _ }
'.'         { Token TokDot _ }
else        { Token TokElse _ }
'='         { Token TokEquals _ }
esac        { Token TokEsac _ }
false       { Token TokFalse _ }
fi          { Token TokFi _ }
ident       { Token (TokIdent _) _ }
if          { Token TokIf _ }
in          { Token TokIn _ }
inherits    { Token TokInherits _ }
int         { Token (TokInt _) _ }
isvoid      { Token TokIsvoid _ }
'<-'        { Token TokLarrow _ }
'{'         { Token TokLbrace _ }
'<='        { Token TokLe _ }
let         { Token TokLet _ }
loop        { Token TokLoop _ }
'('         { Token TokLparen _ }
'<'         { Token TokLt _ }
'-'         { Token TokMinus _ }
new         { Token TokNew _ }
not         { Token TokNot _ }
of          { Token TokOf _ }
'+'         { Token TokPlus _ }
pool        { Token TokPool _ }
'=>'        { Token TokRarrow _ }
'}'         { Token TokRbrace _ }
')'         { Token TokRparen _ }
';'         { Token TokSemi _ }
string      { Token (TokString _) _ }
then        { Token TokThen _ }
'~'         { Token TokTilde _ }
'*'         { Token TokTimes _ }
true        { Token TokTrue _ }
type        { Token (TokType _) _ }
while       { Token TokWhile _ }

%right '<-'
%left not
%nonassoc '<' '<=' '='
%left '+' '-'
%left '*' '/'
%left isvoid
%left '~'
%left '@'
%left '.'

%%

Program :: { PosAST }
        : ClassList    { AST $1 }

ClassList :: { [PosClass] }
          : Class ';' { [$1] }
          | Class ';' ClassList { $1 : $3 }

Class :: { PosClass }
      : class type '{' FeatureList '}'    { Class (idOfTok $2) Nothing $4 }
      | class type inherits type '{' FeatureList '}'
          { Class (idOfTok $2) (Just $ idOfTok $4) $6 }

FeatureList :: { [PosFeature] }
            : {- empty -}               { [] }
            | Feature ';' FeatureList   { $1 : $3 }

Feature :: { PosFeature }
        : ident '(' FormalList ')' ':' type '{' Expr '}'
             { Method (idOfTok $1) $3 (idOfTok $6) $8 }
        | ident ':' type '<-' Expr    { Attribute (mkFormal $1 $3) (Just $5) }
        | ident ':' type              { Attribute (mkFormal $1 $3) Nothing }

FormalList :: { [Formal] }
           : {- empty -}          { [] }
           | FormalListNonempty   { $1 }

FormalListNonempty :: { [Formal] }
                   : Formal                          { [$1] }
                   | Formal ',' FormalListNonempty   { $1 : $3 }

Formal :: { Formal }
       : ident ':' type   { mkFormal $1 $3 }

Expr :: { PosExpr }
     : ident '<-' Expr                { AnnFix (tokenLine $2,
                                                Assign (idOfTok $1) $3) }
     | if Expr then Expr else Expr fi { AnnFix (tokenLine $1, If $2 $4 $6) }
     | while Expr loop Expr pool      { AnnFix (tokenLine $1, While $2 $4) }
     | new type                       { AnnFix (tokenLine $1,
                                                New (idOfTok $2)) }
     | isvoid Expr                    { AnnFix (tokenLine $1, Isvoid $2) }
     | Expr '+' Expr                  { AnnFix (tokenLine $2, Plus $1 $3) }
     | Expr '-' Expr                  { AnnFix (tokenLine $2, Minus $1 $3) }
     | Expr '*' Expr                  { AnnFix (tokenLine $2, Times $1 $3) }
     | Expr '/' Expr                  { AnnFix (tokenLine $2, Divide $1 $3) }
     | '~' Expr                       { AnnFix (tokenLine $1, Negate $2) }
     | Expr '<=' Expr                 { AnnFix (tokenLine $2, Le $1 $3) }
     | Expr '<' Expr                  { AnnFix (tokenLine $2, Lt $1 $3) }
     | Expr '=' Expr                  { AnnFix (tokenLine $2, Eq $1 $3) }
     | not Expr                       { AnnFix (tokenLine $1, Not $2) }
     | '(' Expr ')'                   { $2 }
     | ident                          { AnnFix (tokenLine $1, Id $ idOfTok $1) }
     | int                            { AnnFix (tokenLine $1,
                                                case (unTok $1) of
                                                  TokInt i -> IntConst i) }
     | string                         { AnnFix (tokenLine $1,
                                                case (unTok $1) of
                                                  TokString s -> StringConst s) }
     | true                           { AnnFix (tokenLine $1, BoolConst True) }
     | false                          { AnnFix (tokenLine $1, BoolConst False) }
     | ident '(' ExprList ')'         { AnnFix (tokenLine $1,
                                                SelfDispatch (idOfTok $1) $3) }
     | Expr '.' ident '(' ExprList ')'
         { AnnFix (tokenLine $2, DynamicDispatch $1 (idOfTok $3) $5) }
     | Expr '@' type '.' ident '(' ExprList ')'
         { AnnFix (tokenLine $2,
                   StaticDispatch $1 (idOfTok $3) (idOfTok $5) $7) }
     | '{' ExprSeq '}'                { AnnFix (tokenLine $1, Block $2) }
     | let LetBindingList in Expr     { AnnFix (tokenLine $1, Let $2 $4) }
     | case Expr of CaseList esac     { AnnFix (tokenLine $1, Case $2 $4) }

ExprList :: { [PosExpr] }
         : {- empty -}       { [] }
         | ExprListNonempty  { $1 }

ExprListNonempty :: { [PosExpr] }
                 : Expr                       { [$1] }
                 | ExprListNonempty ',' Expr  { $1 ++ [$3] }

ExprSeq :: { [PosExpr] }
        : Expr ';'           { [$1] }
        | Expr ';' ExprSeq   { $1 : $3 }

LetBindingList :: { [(Formal, Maybe PosExpr)] }
               : LetBinding                     { [$1] }
               | LetBinding ',' LetBindingList  { $1 : $3 }

LetBinding :: { (Formal, Maybe PosExpr) }
           : ident ':' type             { (mkFormal $1 $3, Nothing) }
           | ident ':' type '<-' Expr   { (mkFormal $1 $3, Just $5) }

CaseList :: { [(Formal, PosExpr)] }
         : CaseElem ';'            { [$1] }
         | CaseElem ';' CaseList   { $1 : $3 }

CaseElem :: { (Formal, PosExpr) }
         : ident ':' type '=>' Expr  { (mkFormal $1 $3, $5) }

{

idOfTok :: Token -> Identifier
idOfTok t = case unTok t of
  (TokIdent s) -> Identifier (tokenLine t) s
  (TokType s)  -> Identifier (tokenLine t) s
  _            -> error "idOfTok called on non-identifier"

mkFormal :: Token -> Token -> Formal
mkFormal i t = Formal (idOfTok i) (idOfTok t)

parseError :: Token -> P a
parseError _ = do
  line <- getLineNo
  s <- get
  let symb = aiprev (input s)
  error $ "Parse error on line " ++ show line ++ " near symbol " ++ [symb]

-- Basic classes includes definitions for all the the built-in Cool classes
basicClasses :: [PosClass]
basicClasses =
  [ Class (Identifier 0 "Object") Nothing
          [ Method (Identifier 0 "abort") [] (Identifier 0 "Object")
                   (AnnFix (0, Internal))
          , Method (Identifier 0 "type_name") [] (Identifier 0 "String")
                   (AnnFix (0, Internal))
          , Method (Identifier 0 "copy") [] (Identifier 0 "SELF_TYPE")
                   (AnnFix (0, Internal)) ]
  , Class (Identifier 0 "IO") (Just $ Identifier 0 "Object")
          [ Method (Identifier 0 "out_int")
                   [ Formal (Identifier 0 "x") (Identifier 0 "Int") ]
                   (Identifier 0 "SELF_TYPE") (AnnFix (0, Internal))
          , Method (Identifier 0 "out_string")
                   [ Formal (Identifier 0 "x") (Identifier 0 "String") ]
                   (Identifier 0 "SELF_TYPE") (AnnFix (0, Internal))
          , Method (Identifier 0 "in_int") [] (Identifier 0 "Int")
                   (AnnFix (0, Internal))
          , Method (Identifier 0 "in_string") [] (Identifier 0 "String")
                   (AnnFix (0, Internal)) ]
  , Class (Identifier 0 "Int") (Just $ Identifier 0 "Object") []
  , Class (Identifier 0 "Bool") (Just $ Identifier 0 "Object") []
  , Class (Identifier 0 "String") (Just $ Identifier 0 "Object")
          [ Method (Identifier 0 "length") [] (Identifier 0 "Int")
                   (AnnFix (0, Internal))
          , Method (Identifier 0 "concat")
                   [ Formal (Identifier 0 "s") (Identifier 0 "String") ]
                   (Identifier 0 "String") (AnnFix (0, Internal))
          , Method (Identifier 0 "substr")
                   [ Formal (Identifier 0 "i") (Identifier 0 "Int")
                   , Formal (Identifier 0 "l") (Identifier 0 "Int") ]
                   (Identifier 0 "String") (AnnFix (0, Internal)) ]
  ]

addBasicClasses :: PosAST -> PosAST
addBasicClasses (AST cs) = AST (cs ++ basicClasses)

-- Ensure that any calss that didn't inherit from anything now inherits
-- from Object
inheritObject :: PosAST -> PosAST
inheritObject (AST cs) =
  AST $ map (\(Class n@(Identifier _ name) i fs) ->
               let parent = if name == "Object"
                            then Nothing
                            else Just $ fromMaybe (Identifier 0 "Object") i in
               Class n parent fs) cs

-- In addition to the actual parsing, the parse function adds the basic classes.
-- I think it makes sense to have this be part of the parser because otherwise
-- are forcing the tyepchecker to complete the syntax tree.
parse :: String -> PosAST
parse = inheritObject . addBasicClasses . evalP parserAct

}
