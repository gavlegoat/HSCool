{
module Lexer (lexer) where

import LexParse
import Control.Monad.State
import Data.Char
}

@identifier = [a-z][a-zA-Z0-9_]*
@type = [A-Z][a-zA-Z0-9_]*
@intliteral = [0-9]+

tokens :-

<0>     "@"           { \ _ _ -> mkPlainToken TokAt }
<0>     ":"           { \ _ _ -> mkPlainToken TokColon }
<0>     ","           { \ _ _ -> mkPlainToken TokComma }
<0>     "/"           { \ _ _ -> mkPlainToken TokDivide }
<0>     "."           { \ _ _ -> mkPlainToken TokDot }
<0>     "="           { \ _ _ -> mkPlainToken TokEquals }
<0>     "<-"          { \ _ _ -> mkPlainToken TokLarrow }
<0>     "{"           { \ _ _ -> mkPlainToken TokLbrace }
<0>     "<="          { \ _ _ -> mkPlainToken TokLe }
<0>     "("           { \ _ _ -> mkPlainToken TokLparen }
<0>     "<"           { \ _ _ -> mkPlainToken TokLt }
<0>     "-"           { \ _ _ -> mkPlainToken TokMinus }
<0>     "+"           { \ _ _ -> mkPlainToken TokPlus }
<0>     "=>"          { \ _ _ -> mkPlainToken TokRarrow }
<0>     "}"           { \ _ _ -> mkPlainToken TokRbrace }
<0>     ")"           { \ _ _ -> mkPlainToken TokRparen }
<0>     ";"           { \ _ _ -> mkPlainToken TokSemi }
<0>     "~"           { \ _ _ -> mkPlainToken TokTilde }
<0>     "*"           { \ _ _ -> mkPlainToken TokTimes }

<0>     @identifier   { \ _ s -> mkPlainToken (idLookup s) }
<0>     @type         { \ _ s -> mkPlainToken (typeLookup s) }
<0>     @intliteral   { \ _ s -> getLineNo >>= \l -> mkPlainToken (checkBounds l s) }

<0>     $white+       ;
<0>     "--".*        ;

<0>     \"            { beginString }
<strSC> \\\"          { escapeString }
<strSC> \"            { endString }
<strSC> .             { appendString }

<0,com> "(*"          { beginComment }
<com>   "*)"          { endComment }
<com>   [.\n]         ;

{

mkPlainToken :: TokenType -> P (Maybe Token)
mkPlainToken t = getLineNo >>= return . Just . Token t

lowercase :: String -> String
lowercase = map toLower

idLookup :: String -> TokenType
idLookup s = case (lowercase s) of
  "case"     -> TokCase
  "class"    -> TokClass
  "else"     -> TokElse
  "esac"     -> TokEsac
  "false"    -> TokFalse
  "fi"       -> TokFi
  "if"       -> TokIf
  "in"       -> TokIn
  "inherits" -> TokInherits
  "isvoid"   -> TokIsvoid
  "let"      -> TokLet
  "loop"     -> TokLoop
  "new"      -> TokNew
  "not"      -> TokNot
  "of"       -> TokOf
  "pool"     -> TokPool
  "then"     -> TokThen
  "true"     -> TokTrue
  "while"    -> TokWhile
  _          -> TokIdent s

typeLookup :: String -> TokenType
typeLookup s = case (lowercase s) of
  "case"     -> TokCase
  "class"    -> TokClass
  "else"     -> TokElse
  "esac"     -> TokEsac
  "fi"       -> TokFi
  "if"       -> TokIf
  "in"       -> TokIn
  "inherits" -> TokInherits
  "isvoid"   -> TokIsvoid
  "let"      -> TokLet
  "loop"     -> TokLoop
  "new"      -> TokNew
  "not"      -> TokNot
  "of"       -> TokOf
  "pool"     -> TokPool
  "then"     -> TokThen
  "while"    -> TokWhile
  _          -> TokType s

checkBounds :: Int -> String -> TokenType
checkBounds l s =
  if length s > 10 then error ("Lexer: Integer constant at line " ++ show l ++
                               " too large: " ++ s)
  else if length s < 10 then TokInt (read s)
  else if s < "2147483648" then TokInt (read s)
  else error ("Lexer: Integer constant at line " ++ show l ++ " too large: " ++ s)

beginString :: Int -> String -> P (Maybe Token)
beginString _ _ = do
  s <- get
  put s{lexSC = strSC}
  return Nothing

appendString :: Int -> String -> P (Maybe Token)
appendString _ (c : _) = do
  s <- get
  put s{stringBuf = c:(stringBuf s)}
  return Nothing

escapeString :: Int -> String -> P (Maybe Token)
escapeString _ _ = do
  s <- get
  put s{stringBuf = '"':(stringBuf s)}
  return Nothing

endString :: Int -> String -> P (Maybe Token)
endString l _ = do
  s <- get
  let buf = stringBuf s
  put s{lexSC = 0, stringBuf = ""}
  mkPlainToken (TokString $ reverse buf)

beginComment :: Int -> String -> P (Maybe Token)
beginComment _ _ = do
  s <- get
  put s{lexSC = com, commentDepth = (commentDepth s) + 1}
  return Nothing

endComment :: Int -> String -> P (Maybe Token)
endComment _ _ = do
  s <- get
  let sc = if (commentDepth s) == 1 then 0 else com
  put s{lexSC = sc, commentDepth = (commentDepth s) - 1}
  return Nothing

readToken :: P Token
readToken = do
  s <- get
  case alexScan (input s) (lexSC s) of
    AlexEOF -> if (lexSC s) == com then error "Lexer: End of file in comment"
               else if (lexSC s) == strSC then error "Lexer: End of file in string"
               else return (Token TokEOF 0)
    AlexError i' -> error $ "Lexer: Error on line " ++ (show $ ailineno i')
    AlexSkip i' _ -> do
      put s{input = i'}
      readToken
    AlexToken i' n act -> do
      let (AlexInput {airest=buf}) = input s
      put s{input = i'}
      res <- act n (take n buf)
      case res of
        Nothing -> readToken
        Just t -> return t

lexer :: (Token -> P a) -> P a
lexer cont = readToken >>= cont

}
