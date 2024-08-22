-- | A monad action is a monoid action in the category of endofunctors, what's the problem?
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
import Control.Monad.Trans

-- | Instances must satisfy the following laws:
--
-- * @'lact' '.' 'join' = 'lact' '.' 'fmap' 'lact'@
--
-- * @'lact' '.' 'pure' = 'id'@
class (Monad m, Functor f) => LeftModule m f where
  lact ::
    m (f a) ->
    -- | left monad action
    f a

-- | Instances must satisfy the following laws:
--
-- * @'ract' '.' 'fmap' 'join' = 'ract' '.' 'ract'@
--
-- * @'ract' '.' 'fmap' 'pure' = 'id'@
class (Monad m, Functor f) => RightModule m f where
  ract ::
    f (m a) ->
    -- | right monad action
    f a

-- | Given two monads r and s, an (r, s) bimodule is a functor that is a left module over r and a right module over s, where the two actions are compatible.
--   Instances must satisfy the following law in addition to the laws for @'LeftModule'@ and @'RightModule'@:
--
-- * @'ract' '.' 'lact' = 'lact' '.' 'fmap' 'ract' = 'biact'@
class (LeftModule r f, RightModule s f) => BiModule r s f where
  biact ::
    r (f (s a)) ->
    -- | two-sided monad action
    f a
  biact = ract . lact

instance (Monad m) => RightModule m m where
  ract = join

instance (Monad m) => LeftModule m m where
  lact = join

instance (Monad m) => BiModule m m m where
  biact = join . join

instance RightModule Maybe [] where
  ract = catMaybes

instance LeftModule Maybe [] where
  lact = concat

instance BiModule Maybe Maybe []

instance BiModule Maybe [] []

instance BiModule [] Maybe []

instance (Monad m, Functor f, LeftModule m n) => LeftModule m (Compose n f) where
  lact = Compose . lact . fmap getCompose

instance (Monad m, Functor f, RightModule m n) => RightModule m (Compose f n) where
  ract = Compose . fmap ract . getCompose

instance (Monad s, Monad t, Functor f, LeftModule s u, RightModule t v) => BiModule s t (Compose u (Compose f v))

-- | @'MonadTrans'@ instances are required to satisfy these laws:
--
--   * @'lift' '.' 'pure' = 'pure'@
--
--   * @'lift' (m '>>=' f) = 'lift' m '>>=' ('lift' '.' f)@
--
--   Restating the second law in terms of @'join'@:
--
--   * @'lift' '.' 'join' = 'join' '.' 'fmap' 'lift' '.' 'lift'@
--
--   The left monad action laws can now be easily proved using string diagrams.
--   Functors compose from top to bottom, natural transformations from left to right,
--   @───@ represents @t m@, @┈┈┈@ represents @m@, @├@ represents @'pure'@ or
--   @'join'@ depending on the number of inputs, and @┈┈┈►───@ represents @'lift'@.
--   The @'MonadTrans'@ laws as string diagrams are:
--
--   > ├┈┈┈►───  = ├──────
--
--   > ┈┈┈┐            ┈┈┈►───┐
--   >    ├┈┈┈►───  =         ├───
--   > ┈┈┈┘            ┈┈┈►───┘
--
--   and the diagram for @'lact'@ is:
--
--   > ┈┈►──┐
--   >      ├───
--   > ─────┘
--
--   To prove the identity law:
--
--   >   ├┈┈►──┐          ├─────┐
--   >         ├───  =          ├───  =  ──────
--   > ────────┘        ────────┘
--
--   In other words,
--
--   @   'lact' '.' 'pure'
--   = 'join' '.' 'lift' '.' 'pure'
--   = 'join' '.' 'pure'
--   = 'id'@
--
--   To prove associativity:
--
--   > ┈┈┈┐              ┈┈►──┐
--   >    ├┈┈►─┐              ├──┐         ┈┈┈┈┈┈┈►─┐
--   > ┈┈┈┘    ├────  =  ┈┈►──┘  ├────  =  ┈┈►──┐   ├────
--   > ────────┘         ────────┘              ├───┘
--   >                                     ─────┘
--
--   In other words,
--
--   @  'lact' '.' 'join'
--   = 'join' '.' 'lift' '.' 'join'
--   = 'join' '.' 'join' '.' 'fmap' 'lift' '.' 'lift'
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' 'lift' '.' 'lift'
--   = 'join' '.' 'fmap' ('join' '.' 'lift') '.' 'lift'
--   = 'join' '.' 'lift' '.' 'fmap' ('join' '.' 'lift')
--   = 'lact' '.' 'fmap' 'lact'@
instance (MonadTrans t, Monad m, Monad (t m)) => LeftModule m (t m) where
  lact = join . lift

-- | We prove the right module laws using string diagrams, just as in the case
--   of the left module laws.
--
--   The diagram for @'ract'@ is:
--
--   > ─────┐
--   >      ├───
--   > ┈┈►──┘
--
--   To prove the identity law:
--
--   > ────────┐        ────────┐
--   >         ├───  =          ├───  =  ──────
--   >   ├┈┈►──┘          ├─────┘
--
--   In other words,
--
--   @   'ract' '.' 'fmap' 'pure'
--   = 'join' '.' 'fmap' 'lift' , 'pure'
--   = 'join' '.' 'fmap' 'lift' , 'fmap' 'pure'
--   = 'join' '.' 'fmap' ('lift' , 'pure')
--   = 'join' '.' 'fmap' 'pure'
--   = 'id'@
--
--   To prove associativity:
--
--   >                                      ─────┐
--   > ────────┐         ─────────┐              ├───┐
--   > ┈┈┈┐    ├────  =  ┈┈►──┐   ├────  =  ┈┈►──┘   ├────
--   >    ├┈┈►─┘              ├───┘         ┈┈┈┈┈┈┈►─┘
--   > ┈┈┈┘              ┈┈►──┘
--
--   In other words,
--
--   @  'ract' '.' 'fmap' 'join'
--   = 'join' '.' 'fmap' 'lift' '.' 'fmap' 'join'
--   = 'join' '.' 'fmap' ('lift' '.' 'join')
--   = 'join' '.' 'fmap' ('join' '.' 'fmap' 'lift' '.' 'lift')
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' ('fmap' 'lift' '.' 'lift')
--   = 'join' '.' 'join' '.' 'fmap' ('fmap' 'lift') '.' 'fmap' ('lift')
--   = 'join' '.' 'fmap' 'lift' '.' 'join' '.' 'fmap' 'lift'
--   = 'ract' '.' 'ract'@
instance (MonadTrans t, Monad m, Monad (t m)) => RightModule m (t m) where
  ract = (lift =<<)

-- | We prove the bimodule law using string diagrams, just as in the case
--   of the left and right module laws:
--
--   > ┈┈►─┐
--   >     ├───┐          ┈┈┈┈┈┈►─┐
--   > ────┘   ├────  =   ────┐   ├────
--   > ┈┈┈┈┈┈►─┘              ├───┘
--   >                    ┈┈►─┘
--
--   In other words,
--
--   @  'biact'
--   = 'ract' '.' 'lact'
--   = 'join' '.' 'fmap' 'lift' '.' 'join' '.' 'lift'
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' ('fmap' 'lift') '.' 'lift'
--   = 'join' '.' 'fmap' ('join' '.' 'fmap' 'lift') '.' 'lift'
--   = 'join' '.' 'fmap' 'ract' '.' 'lift'
--   = 'join' '.' 'lift' '.' 'fmap' 'ract'
--   = 'lact' '.' 'fmap' 'ract'@
instance (MonadTrans t, Monad m, Monad (t m)) => BiModule m m (t m) where
