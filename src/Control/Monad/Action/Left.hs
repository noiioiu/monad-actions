{-# LANGUAGE AllowAmbiguousTypes #-}

module Control.Monad.Action.Left ((>>=), (>>), pure, return, fail, join) where

import Control.Monad.Action
import Prelude hiding (return, (>>), (>>=))

(>>=) :: (LeftModule m f) => m a -> (a -> f b) -> f b
(>>=) = (ljoin .) . flip fmap

(>>) :: (LeftModule m f) => m a -> f b -> f b
(>>) = (ljoin .) . flip (fmap . const)

return :: (Applicative f) => a -> f a
return = pure

join :: (LeftModule m f) => m (f a) -> f a
join = ljoin
