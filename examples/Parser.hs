{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecordWildCards #-}

import Control.Applicative (Alternative (..))
import Control.Monad (void)
import Control.Monad.Action.Records
import Control.Monad.State (MonadState (..), StateT (..), evalStateT, execStateT)
import Data.List (uncons)
import GHC.Records (HasField (..))
import Prelude hiding ((<*>), (=<<), (>>), (>>=))
import Prelude qualified as P

ifThenElse :: Bool -> a -> a -> a
ifThenElse = \case
  True -> const
  False -> const id

type Parser = StateT String Maybe

getText :: Parser String
getText = get

putText :: String -> Parser ()
putText = put

-- Parser that returns a single character satisfying a predicate
satisfy :: (Char -> Bool) -> Parser Char
satisfy p =
  let LeftAction {..} = transformerStackAction.left
   in do
        t <- getText
        (c, t') <- uncons t
        putText t'
        if p c then pure c else empty

char :: Char -> Parser Char
char = satisfy . (==)

string :: String -> Parser String
string = traverse char

eof :: Parser ()
eof =
  getText P.>>= \case
    "" -> pure ()
    _ -> empty

balancedBrackets :: StateT (Int, Int) Parser ()
balancedBrackets =
  let LeftAction {..} = transformerStackAction.left
      pair :: StateT (Int, Int) Parser ()
      pair =
        do
          char '('
          (depth, maxDepth) <- get @_ @(StateT (Int, Int) Parser)
          put @_ @(StateT (Int, Int) Parser) (depth + 1, max maxDepth $ depth + 1)
          many pair
          char ')'
          (_, maxDepth') <- get @_ @(StateT (Int, Int) Parser)
          put (depth, maxDepth')
   in void $ many pair >> (eof >>= pure)

main :: IO ()
main =
  let parser = execStateT balancedBrackets (0, 0)
   in getLine P.>>= (\case Just (_, m) -> print m; Nothing -> error "unbalanced brackets or non-bracket character") . evalStateT parser
