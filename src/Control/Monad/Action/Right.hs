{-# LANGUAGE RebindableSyntax #-}

module Control.Monad.Action.Right (return, (>>=), (>>)) where

import Control.Monad.Action
import Prelude hiding (return, (>>), (>>=))

return :: (Applicative f) => a -> f a
return = pure

(>>=) :: (RightModule m f) => f a -> (a -> m b) -> f b
(>>=) = (ract .) . flip fmap

(>>) :: (RightModule m f) => f a -> m b -> f b
(>>) = (ract .) . flip (fmap . const)
