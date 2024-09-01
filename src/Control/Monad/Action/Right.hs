{-# LANGUAGE RebindableSyntax #-}

module Control.Monad.Action.Right (return, (>>=), (>>)) where

import Control.Monad.Action
import Data.Pointed
import Prelude hiding (return, (>>), (>>=))

return :: (Pointed f) => a -> f a
return = point

(>>=) :: (RightModule m f) => f a -> (a -> m b) -> f b
(>>=) = (ract .) . flip fmap

(>>) :: (RightModule m f) => f a -> m b -> f b
(>>) = (ract .) . flip (fmap . const)
