{-# LANGUAGE RebindableSyntax #-}

module Control.Monad.Action.Left (return, (>>=), (>>)) where

import Control.Monad.Action
import Data.Pointed
import Prelude hiding (return, (>>), (>>=))

-- Pointed should be a superclass of Applicative
return :: (Pointed f) => a -> f a
return = point

(>>=) :: (LeftModule m f) => m a -> (a -> f b) -> f b
(>>=) = (lact .) . flip fmap

(>>) :: (LeftModule m f) => m a -> f b -> f b
(>>) = (lact .) . flip (fmap . const)
