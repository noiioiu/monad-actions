module Control.Monad.Action.Left ((>>=), (>>), pure, return, fail) where

import Control.Monad.Action
import Prelude hiding ((>>), (>>=))

(>>=) :: (LeftModule m f) => m a -> (a -> f b) -> f b
(>>=) = (lact .) . flip fmap

(>>) :: (LeftModule m f) => m a -> f b -> f b
(>>) = (lact .) . flip (fmap . const)
