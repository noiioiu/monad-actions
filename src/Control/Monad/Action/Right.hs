{-# LANGUAGE MonoLocalBinds #-}

-- | This module should be imported qualified, and can be used with the @QualifiedDo@ extension.
module Control.Monad.Action.Right ((>>=), (>>), (=<<), (>=>), (<=<), (<*>), fmap, pure, return, fail, join) where

import Control.Monad.Action
import Prelude hiding (fmap, pure, return, (<*>), (=<<), (>>), (>>=))
import Prelude qualified as P

infixl 1 >>=

(>>=) :: (RightModule m f) => f a -> (a -> m b) -> f b
(>>=) = rbind

infixr 1 =<<

(=<<) :: (RightModule m f) => (a -> m b) -> f a -> f b
(=<<) = flip rbind

infixl 1 >>

(>>) :: (RightModule m f) => f a -> m b -> f b
(>>) = (. const) . rbind

infixr 1 >=>

(>=>) :: (RightModule m f) => (a -> f b) -> (b -> m c) -> a -> f c
(>=>) = flip $ (.) . (=<<)

infixr 1 <=<

(<=<) :: (RightModule m f) => (b -> m c) -> (a -> f b) -> a -> f c
(<=<) = (.) . (=<<)

fmap :: (Functor f) => (a -> b) -> f a -> f b
fmap = P.fmap

pure :: (Applicative f) => a -> f a
pure = P.pure

return :: (Applicative f) => a -> f a
return = pure

join :: (RightModule m f) => f (m a) -> f a
join = rjoin

infixl 4 <*>

(<*>) :: (RightModule m f) => f (a -> b) -> m a -> f b
fs <*> xs = fs >>= flip fmap xs
