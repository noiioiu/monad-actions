-- | A monad action is just a monoid action in the category of endofunctors, what's the problem?
module Control.Monad.Action
  ( module Control.Monad,
    LeftModule (..),
    RightModule (..),
  )
where

import Control.Monad

-- | Instances must satisfy the following laws:
--
-- * @'lscale' '.' 'join' = 'lscale' '.' 'fmap' 'lscale'@
--
-- * @'lscale' . 'return' = 'id'@
class LeftModule f m a where
  lscale ::
    m (f a) ->
    -- | left "scalar multiplication"
    f a

-- | Instances must satisfy the following laws:
--
-- * @'rscale' . 'fmap' 'join' = 'rscale' . 'rscale'@
--
-- * @'rscale' . 'fmap' 'return' = 'id'@
class RightModule f m a where
  rscale ::
    f (m a) ->
    -- | right "scalar multiplication"
    f a
