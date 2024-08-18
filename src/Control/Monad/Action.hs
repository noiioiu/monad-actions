-- | A monad action is just a monoid action in the category of endofunctors, what's the problem?
module Control.Monad.Action
  ( module Control.Monad,
    LeftModule (..),
    RightModule (..),
    BiModule (..),
  )
where

import Control.Monad
import Data.Functor.Compose
import Data.Maybe (catMaybes)

-- | Instances must satisfy the following laws:
--
-- * @'lact' '.' 'join' = 'lact' '.' 'fmap' 'lact'@
--
-- * @'lact' . 'return' = 'id'@
class (Monad m, Functor f) => LeftModule m f where
  lact ::
    m (f a) ->
    -- | left monad action
    f a

-- | Instances must satisfy the following laws:
--
-- * @'ract' . 'fmap' 'join' = 'ract' . 'ract'@
--
-- * @'ract' . 'fmap' 'return' = 'id'@
class (Monad m, Functor f) => RightModule m f where
  ract ::
    f (m a) ->
    -- | right monad action
    f a

-- | Given two monads r and s, an (r, s) bimodule is a functor that is a left module over r and a right module over s, where the two actions are compatible.
--   Instances must satisfy the following law in addition to the laws for @'LeftModule'@ and @'RightModule'@:
--
-- * @'ract' . 'lact' = 'lact' . 'fmap' 'ract' = 'biact'@
class (LeftModule r f, RightModule s f) => BiModule r s f where
  biact ::
    r (f (s a)) ->
    -- | two-sided monad action
    f a

instance (Monad m) => RightModule m m where
  ract = join

instance (Monad m) => LeftModule m m where
  lact = join

instance (Monad m) => BiModule m m m where
  biact = join . join

instance RightModule Maybe [] where
  ract = catMaybes

instance LeftModule Maybe [] where
  lact Nothing = []
  lact (Just l) = l

instance BiModule Maybe Maybe [] where
  biact = ract . lact

instance (Monad m, Functor f, LeftModule m n) => LeftModule m (Compose n f) where
  lact = Compose . lact . fmap getCompose

instance (Monad m, Functor f, RightModule m n) => RightModule m (Compose f n) where
  ract = Compose . fmap ract . getCompose

instance (Monad s, Monad t, Functor f, LeftModule s u, RightModule t v) => BiModule s t (Compose u (Compose f v)) where
  biact = Compose . fmap (Compose . fmap ract) . lact . fmap (fmap getCompose . getCompose)
