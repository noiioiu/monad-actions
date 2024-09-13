module Control.Monad.Action.Right ((>>=), (>>), pure, return, fail, join) where

import Control.Monad.Action
import Prelude hiding (return, (>>), (>>=))

(>>=) :: (RightModule m f) => f a -> (a -> m b) -> f b
(>>=) = (ract .) . flip fmap

(>>) :: (RightModule m f) => f a -> m b -> f b
(>>) = (ract .) . flip (fmap . const)

return :: (Applicative f) => a -> f a
return = pure

join :: (RightModule m f) => f (m a) -> f a
join = ract
