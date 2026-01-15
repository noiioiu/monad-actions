-- | This module is meant to be used with the @QualifiedDo@ extension.
module Control.Monad.Action.Left ((>>=), (>>), (=<<), (>=>), (<=<), (<*>), fmap, pure, return, fail, join) where

import Control.Monad.Action
import Prelude hiding (fmap, pure, return, (<*>), (=<<), (>>), (>>=))
import Prelude qualified as P

infixl 1 >>=

(>>=) :: (LeftModule m f) => m a -> (a -> f b) -> f b
(>>=) = lbind

infixr 1 =<<

(=<<) :: (LeftModule m f) => (a -> f b) -> m a -> f b
(=<<) = flip lbind

infixl 1 >>

(>>) :: (LeftModule m f) => m a -> f b -> f b
(>>) = (. const) . lbind

infixr 1 >=>

(>=>) :: (LeftModule m f) => (a -> m b) -> (b -> f c) -> a -> f c
(>=>) = flip $ (.) . (=<<)

infixr 1 <=<

(<=<) :: (LeftModule m f) => (b -> f c) -> (a -> m b) -> a -> f c
(<=<) = (.) . (=<<)

fmap :: (Functor f) => (a -> b) -> f a -> f b
fmap = P.fmap

pure :: (Applicative f) => a -> f a
pure = P.pure

return :: (Applicative f) => a -> f a
return = pure

join :: (LeftModule m f) => m (f a) -> f a
join = ljoin

infixl 4 <*>

(<*>) :: (LeftModule m f) => m (a -> b) -> f a -> f b
fs <*> xs = fs >>= flip fmap xs
