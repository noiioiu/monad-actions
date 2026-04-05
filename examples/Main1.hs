{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Monad (forM)
import Control.Monad.Action.Records
import Control.Monad.Codensity (Codensity (..))
import Control.Monad.Except
import Control.Monad.State (MonadState (..), State, StateT, execStateT)
import Data.Bifunctor (Bifunctor (..))
import Data.List.NonEmpty qualified as NE
import GHC.Records
import Prelude hiding ((<*>), (=<<), (>>), (>>=))
import Prelude qualified as P

nums :: [Integer]
nums =
  let LeftAction {..} = submonadAction.left
   in do
        -- variables can be bound from any submonad of []
        a <- Just 8
        b <- NE.fromList [1, 2, 3, 4, 5]
        c <- [0, 1]
        pure $ a * b + c

st :: ExceptT Int Maybe String
st =
  let LeftAction {..} = submonadAction.left
   in do
        n <- Right 8
        pure $ show n

toCodensity :: (Monad m) => m a -> Codensity m a
toCodensity m = Codensity (m P.>>=)

fromCodensity :: (Monad m) => Codensity m a -> m a
fromCodensity (Codensity f) = f pure

pair :: (Char, Integer)
pair =
  let LeftAction {..} = codensityAction
   in do
        k <- Codensity (\f -> first succ $ f 8) :: Codensity ((,) Char) Integer
        ('a', k)

main :: IO ()
main =
  print pair
    P.>> P.do
      f <-
        flip execStateT (0 :: Integer) $
          let BiAction {left = LeftAction {..}} = submonadAction
           in forM nums $
                \n -> do
                  s <- get @Integer @(State Integer)
                  print n
                  put $ s + n
      print f
