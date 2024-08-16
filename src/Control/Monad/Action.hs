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
-- * @'lscale' '.' 'join' = 'lscale' '.' 'fmap' 'lscale'@
--
-- * @'lscale' . 'return' = 'id'@
class (Monad m) => LeftModule m f where
  lscale ::
    m (f a) -> f a -- ^ left "scalar multiplication"

-- | Instances must satisfy the following laws:
--
-- * @'rscale' . 'fmap' 'join' = 'rscale' . 'rscale'@
--
-- * @'rscale' . 'fmap' 'return' = 'id'@
class (Monad m) => RightModule m f where
  rscale ::
    f (m a) -> f a -- ^ right "scalar multiplication"

-- | Given two monads r and s, an (r, s) bimodule is a functor that is a left module over r and a right module over s, where the two "scalar multiplications" are compatible.
--   Instances must satisfy the following law in addition to the laws for @'LeftModule'@ and @'RightModule'@:
--
-- * @'rscale' . 'lscale' = 'lscale' . 'fmap' 'rscale' = 'biscale'@
class (LeftModule r f, RightModule s f) => BiModule r s f where
  biscale :: r (f (s a)) -> f a -- ^ two-sided "scalar multiplication"
