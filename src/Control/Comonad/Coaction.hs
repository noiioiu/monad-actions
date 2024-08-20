-- | A comonad coaction is a comonoid action in the category of endofunctors, what's the problem?
module Control.Comonad.Coaction
  ( module Control.Comonad,
    LeftComodule (..),
    RightComodule (..),
    BiComodule (..),
  )
where

import Control.Comonad
import Data.Functor.Compose

-- | Instances must satisfy the following laws:
--
-- * @'duplicate' '.' 'lcoact' = 'fmap' 'lcoact' '.' 'lcoact'@
--
-- * @'extract' '.' 'lcoact' = 'id'@
class (Comonad w, Functor f) => LeftComodule w f where
  lcoact ::
    f a ->
    -- | left comonad coaction
    w (f a)

-- | Instances must satisfy the following laws:
--
-- * @'fmap' 'duplicate' '.' 'rcoact' = 'rcoact' '.' 'rcoact'@
--
-- * @'fmap' 'extract' '.' 'lcoact' = 'id'@
class (Comonad w, Functor f) => RightComodule w f where
  rcoact ::
    f a ->
    -- | right comonad coaction
    f (w a)

-- | Given two comonads r and s, an (r, s) bicomodule is a functor that is a left comodule over r and a right comodule over s, where the two coactions are compatible.
--   Instances must satisfy the following law in addition to the laws for @'LeftComodule'@ and @'RightComodule'@:
--
-- * @'lcoact' '.' 'rcoact' = 'fmap' 'rcoact' '.' 'lcoact' = 'bicoact'@
class (LeftComodule r f, RightComodule s f) => BiComodule r s f where
  bicoact ::
    f a ->
    -- | two-sided comonad coaction
    r (f (s a))
  bicoact = lcoact . rcoact

instance (Comonad w) => LeftComodule w w where
  lcoact = duplicate

instance (Comonad w) => RightComodule w w where
  rcoact = duplicate

instance (Comonad w) => BiComodule w w w where
 bicoact = duplicate . duplicate

instance (Comonad w, Functor f, LeftComodule w v) => LeftComodule w (Compose v f) where
  lcoact = fmap Compose . lcoact . getCompose

instance (Comonad w, Functor f, RightComodule w v) => RightComodule w (Compose f v) where
  rcoact = Compose . fmap rcoact . getCompose

instance (Comonad s, Comonad t, Functor f, LeftComodule s u, RightComodule t v) => BiComodule s t (Compose u (Compose f v))
