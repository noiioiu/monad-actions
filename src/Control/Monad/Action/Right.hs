-- | This module is meant to be used with the @QualifiedDo@ extension.
module Control.Monad.Action.Right ((>>=), (>>), (=<<), (>=>), (<=<), pure, return, fail, join) where

import Control.Monad.Action
import Prelude hiding (return, (=<<), (>>), (>>=))

(>>=) :: (RightModule m f) => f a -> (a -> m b) -> f b
(>>=) = (rjoin .) . flip fmap

(=<<) :: (RightModule m f) => (a -> m b) -> f a -> f b
(=<<) = (rjoin .) . fmap

(>>) :: (RightModule m f) => f a -> m b -> f b
(>>) = (rjoin .) . flip (fmap . const)

(>=>) :: (RightModule m f) => (a -> f b) -> (b -> m c) -> a -> f c
(>=>) = flip $ (.) . (=<<)

(<=<) :: (RightModule m f) => (b -> m c) -> (a -> f b) -> a -> f c
(<=<) = (.) . (=<<)

return :: (Applicative f) => a -> f a
return = pure

join :: (RightModule m f) => f (m a) -> f a
join = rjoin
