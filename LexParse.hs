{- This module along with parts of the lexer are taken from the examples at
 - github.com/jmoy/alexhappy.
 -}

module LexParse where

import Control.Monad.State
import Control.Monad
import Data.Word
import Data.Int
import Codec.Binary.UTF8.String (encode)

data TokenType =
    TokAt
  | TokCase
  | TokClass
  | TokColon
  | TokComma
  | TokDivide
  | TokDot
  | TokElse
  | TokEquals
  | TokEsac
  | TokFalse
  | TokFi
  | TokIdent String
  | TokIf
  | TokIn
  | TokInherits
  | TokInt Int32
  | TokIsvoid
  | TokLarrow
  | TokLbrace
  | TokLe
  | TokLet
  | TokLoop
  | TokLparen
  | TokLt
  | TokMinus
  | TokNew
  | TokNot
  | TokOf
  | TokPlus
  | TokPool
  | TokRarrow
  | TokRbrace
  | TokRparen
  | TokSemi
  | TokString String
  | TokThen
  | TokTilde
  | TokTimes
  | TokTrue
  | TokType String
  | TokWhile
  | TokEOF
  deriving (Eq, Show)

data Token = Token { unTok :: TokenType, tokenLine :: Int }

data AlexInput = AlexInput
  { aiprev :: Char
  , aibytes :: [Word8]
  , airest :: String
  , ailineno :: Int
  } deriving (Show)

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte ai = case (aibytes ai) of
  (b : bs) -> Just (b, ai{aibytes=bs})
  [] -> case (airest ai) of
    (c : cs) -> let n  = ailineno ai
                    n' = if (c == '\n') then n + 1 else n
                    (b : bs) = encode [c]
                in Just (b, AlexInput { aiprev = c
                                      , aibytes = bs
                                      , airest = cs
                                      , ailineno = n' })
    [] -> Nothing

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (AlexInput {aiprev=c}) = c

data ParseState = ParseState
  { input :: AlexInput
  , lexSC :: Int
  , commentDepth :: Int
  , stringBuf :: String
  } deriving (Show)

initialState :: String -> ParseState
initialState s = ParseState { input = AlexInput { aiprev = '\n'
                                                , aibytes = []
                                                , airest = s
                                                , ailineno = 1 }
                            , lexSC = 0
                            , commentDepth = 0
                            , stringBuf = "" }

type P a = State ParseState a

getLineNo :: P Int
getLineNo = get >>= (return . ailineno . input)

evalP :: P a -> String -> a
evalP m s = evalState m (initialState s)
