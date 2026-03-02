{-# LANGUAGE MonoLocalBinds #-}

-- |
-- Module      : Control.Monad.Action.Right
-- Description : operators for right monad actions
-- Copyright   : © noiioiu
-- License     : LGPL-2
-- Maintainer  : noiioiu@cocaine.ninja
-- Stability   : experimental
-- Portability : not portable
--
-- Operators for right monad actions.
-- This module should be imported qualified, and can be used with the @QualifiedDo@ extension.
module Control.Monad.Action.Right
  ( (>>=),
    (>>),
    (=<<),
    (>=>),
    (<=<),
    (<*>),
    fmap,
    pure,
    return,
    fail,
    join,
    mfix,
  )
where

import Control.Monad.Action
import Control.Monad.Fix qualified as F
import GHC.Stack (HasCallStack)
import Prelude hiding (fail, fmap, pure, return, (<*>), (=<<), (>>), (>>=))
import Prelude qualified as P

infixl 1 >>=

-- | @'rbind'@ in operator form.
(>>=) :: (RightModule m f) => f a -> (a -> m b) -> f b
(>>=) = rbind

infixr 1 =<<

-- | @'rbind'@ with arguments swapped.
(=<<) :: (RightModule m f) => (a -> m b) -> f a -> f b
(=<<) = flip rbind

infixl 1 >>

-- | Sequencing operator induced by a right monad action.
(>>) :: (RightModule m f) => f a -> m b -> f b
(>>) = (. const) . rbind

infixr 1 >=>

-- | Left to right Kleisli arrow scalar multiplication induced by a right monad action.
(>=>) :: (RightModule m f) => (a -> f b) -> (b -> m c) -> a -> f c
(>=>) = flip $ (.) . (=<<)

infixr 1 <=<

-- | Right to left Kleisli arrow scalar multiplication induced by a right monad action.
(<=<) :: (RightModule m f) => (b -> m c) -> (a -> f b) -> a -> f c
(<=<) = (.) . (=<<)

-- | Alias for @'rjoin'@.
join :: (RightModule m f) => f (m a) -> f a
join = rjoin

-- | Re-export from "Prelude".
fmap :: (Functor f) => (a -> b) -> f a -> f b
fmap = P.fmap

-- | Re-export from "Prelude".
pure :: (Applicative f) => a -> f a
pure = P.pure

-- | Re-export from "Prelude".
fail :: (HasCallStack, MonadFail m) => String -> m a
fail = P.fail

-- | Re-export from "Control.Monad.Fix".
mfix :: (F.MonadFix m) => (a -> m a) -> m a
mfix = F.mfix

-- | Alias for @'pure'@.
return :: (Applicative f) => a -> f a
return = pure

infixl 4 <*>

-- | Used for desugaring qualified @do@ blocks when @ApplicativeDo@ is enabled.
(<*>) :: (RightModule m f) => f (a -> b) -> m a -> f b
fs <*> xs = fs >>= flip fmap xs
