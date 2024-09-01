{-# LANGUAGE RebindableSyntax #-}

module Control.Monad.Action.Left (return, (>>=), (>>)) where

import Control.Monad.Action
import Prelude hiding (return, (>>), (>>=))

return :: (Applicative f) => a -> f a
return = pure

(>>=) :: (LeftModule m f) => m a -> (a -> f b) -> f b
(>>=) = (lact .) . flip fmap

(>>) :: (LeftModule m f) => m a -> f b -> f b
(>>) = (lact .) . flip (fmap . const)
