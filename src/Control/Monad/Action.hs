-- | A monad action is just a monoid action in the category of endofunctors, what's the problem?
module Control.Monad.Action
  ( module Control.Monad,
    LeftModule (..),
    RightModule (..),
    BiModule (..),
  )
where

import Control.Monad

-- | Instances must satisfy the following laws:
--
-- * @'lact' '.' 'join' = 'lact' '.' 'fmap' 'lact'@
--
-- * @'lact' . 'return' = 'id'@
class (Monad m, Functor f) => LeftModule m f where
  lact ::
    m (f a) -> f a -- ^ left monad action

-- | Instances must satisfy the following laws:
--
-- * @'ract' . 'fmap' 'join' = 'ract' . 'ract'@
--
-- * @'ract' . 'fmap' 'return' = 'id'@
class (Monad m, Functor f) => RightModule m f where
  ract ::
    f (m a) -> f a -- ^ right monad action

-- | Given two monads r and s, an (r, s) bimodule is a functor that is a left module over r and a right module over s, where the two actions are compatible.
--   Instances must satisfy the following law in addition to the laws for @'LeftModule'@ and @'RightModule'@:
--
-- * @'ract' . 'lact' = 'lact' . 'fmap' 'ract' = 'biact'@
class (LeftModule r f, RightModule s f) => BiModule r s f where
  biact :: r (f (s a)) -> f a -- ^ two-sided monad action
