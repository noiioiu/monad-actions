{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE UndecidableInstances #-}

{- HLINT ignore "Redundant pure" -}

module Main (main) where

import Control.Applicative
import Control.Monad
import Control.Monad.Action
import Control.Monad.Action.Left qualified as L
import Control.Monad.Action.Right qualified as R
import Control.Monad.State hiding (get, put)
import Control.Monad.State qualified as State
import Data.Char
import Data.Complex
import Data.Functor
import Data.List
import System.IO
import Text.Read hiding (get)

newtype Parser a = Parser {getParser :: StateT String Maybe a}
  deriving (Functor, Applicative, Alternative, Monad, MonadState String)

runParser :: Parser a -> String -> Maybe a
runParser = evalStateT . getParser

instance {-# INCOHERENT #-} (Monad m, LeftModule m (StateT String Maybe)) => LeftModule m Parser where
  ljoin = Parser . ljoin . fmap getParser

instance {-# INCOHERENT #-} (Monad m, RightModule m (StateT String Maybe)) => RightModule m Parser where
  rjoin = Parser . rjoin . getParser

instance {-# INCOHERENT #-} (Functor f, LeftModule (StateT String Maybe) f) => LeftModule Parser f where
  ljoin = ljoin . getParser

instance {-# INCOHERENT #-} (Functor f, RightModule (StateT String Maybe) f) => RightModule Parser f where
  rjoin = rjoin . fmap getParser

get :: State s s
get = State.get

put :: s -> State s ()
put = State.put

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = L.do
  s <- get
  (c, s') <- uncons s
  put s'
  if p c then pure c else empty

char :: Char -> Parser Char
char = satisfy . (==)

string :: String -> Parser String
string = traverse char

eof :: Parser ()
eof = L.do
  s <- get
  unless (null s) empty

num :: (Read a, Fractional a) => Parser a
num = R.do
  s <- some (satisfy (`elem` ('.' : ['0' .. '9'])))
  readMaybe s

chainl1 :: (Alternative f, Monad f) => f t -> f (t -> t -> t) -> f t
chainl1 p o = p >>= rest
  where
    rest x =
      ( o >>= \f ->
          p >>= \y -> rest $ f x y
      )
        <|> pure x

chainr1 :: (Alternative f, Monad f) => f t -> f (t -> t -> t) -> f t
chainr1 p o =
  p
    >>= \x ->
      ( fmap ($ x) o
          <*> chainr1 p o
      )
        <|> pure x

addOp :: (Num a) => Parser (a -> a -> a)
addOp = char '+' $> (+) <|> char '-' $> (-)

multOp :: (Fractional a) => Parser (a -> a -> a)
multOp = char '*' $> (*) <|> char '/' $> (/)

powerOp :: (Floating a) => Parser (a -> a -> a)
powerOp = (string "^" <|> string "**") $> (**)

func :: (Floating a) => Parser (a -> a)
func =
  string "exp" $> exp
    <|> string "log" $> log
    <|> string "sqrt" $> sqrt
    <|> string "sin" $> sin
    <|> string "cos" $> cos
    <|> string "tan" $> tan
    <|> string "asin" $> asin
    <|> string "acos" $> acos
    <|> string "atan" $> atan
    <|> string "sinh" $> sinh
    <|> string "cosh" $> cosh
    <|> string "tanh" $> tanh
    <|> string "asinh" $> asinh
    <|> string "acosh" $> acosh
    <|> string "atanh" $> atanh

constant :: (RealFloat a) => Parser (Complex a)
constant = string "pi" $> pi <|> string "e" $> exp 1 <|> char 'i' $> (0 :+ 1)

skipSpaces :: Parser a -> Parser a
skipSpaces p = many (satisfy isSpace) *> p <* many (satisfy isSpace)

complexExpr :: (RealFloat a, Read a) => Parser (Complex a)
complexExpr = chainl1 summand addOp
  where
    summand = chainl1 factor multOp
    factor = do
      sign <- skipSpaces $ fmap (maybe 1 (\case '-' -> -1; _ -> 1)) . optional $ satisfy (`elem` "+-")
      p <- chainl1 implicitFactor $ many (satisfy isSpace) $> (*)
      pure $ sign * p
    implicitFactor = chainr1 operand powerOp
    operand =
      skipSpaces $
        fmap (:+ 0) num
          <|> func <*> factor
          <|> constant
          <|> (char '(' *> complexExpr <* char ')')

toString :: (Num a, Eq a, Show a, Ord a) => Complex a -> String
toString = \case
  (0 :+ 0) -> "0"
  (0 :+ 1) -> "i"
  (0 :+ (-1)) -> "-i"
  (0 :+ y) -> show' y ++ " i"
  (x :+ 0) -> show' x
  (x :+ 1) -> show' x ++ " + i"
  (x :+ (-1)) -> show' x ++ " - i"
  (x :+ y) -> show' x ++ (if y >= 0 then " + " else " - ") ++ show' (abs y) ++ " i"
  where
    show' = reverse . dropWhile (`elem` "0.") . reverse . show

main :: IO ()
main = forever $ do
  putStr "> "
  hFlush stdout
  x <- getLine
  let g = runParser (complexExpr @Double <* eof) x
  maybe (hPutStrLn stderr "?") (putStrLn . toString) g
