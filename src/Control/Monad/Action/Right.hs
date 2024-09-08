module Control.Monad.Action.Right ((>>=), (>>), pure, return, fail) where

import Control.Monad.Action
import Prelude hiding ((>>), (>>=))

(>>=) :: (RightModule m f) => f a -> (a -> m b) -> f b
(>>=) = (ract .) . flip fmap

(>>) :: (RightModule m f) => f a -> m b -> f b
(>>) = (ract .) . flip (fmap . const)
