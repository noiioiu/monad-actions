-- | A monad action is a monoid action in the category of endofunctors, what's the problem?
module Control.Monad.Action
  ( module Control.Monad,
    LeftModule (..),
    RightModule (..),
    BiModule (..),
  )
where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Functor.Compose
import Data.Maybe (catMaybes)

-- | Instances must satisfy the following laws:
--
-- * @'lact' '.' 'join' = 'lact' '.' 'fmap' 'lact'@
--
-- * @'lact' '.' 'return' = 'id'@
class (Monad m, Functor f) => LeftModule m f where
  lact ::
    m (f a) ->
    -- | left monad action
    f a

-- | Instances must satisfy the following laws:
--
-- * @'ract' '.' 'fmap' 'join' = 'ract' '.' 'ract'@
--
-- * @'ract' '.' 'fmap' 'return' = 'id'@
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

instance (Monad m) => RightModule m (StateT s m) where
  ract = StateT . fmap (uncurry (flip (fmap . flip (,))) =<<) . runStateT

instance (Monad m) => RightModule m (ReaderT r m) where
  ract = ReaderT . fmap join . runReaderT

instance (Monad m) => LeftModule m (WriterT w m) where
  lact = WriterT . (runWriterT =<<)

-- | @'MonadIO'@ instances are required to satisfy these laws in addition to the @'Monad'@ laws:
--
--   * @'liftIO' '.' 'return' = 'return'@
--
--   * @'liftIO' (m '>>=' f) = 'liftIO' m '>>=' ('liftIO' '.' f)@
--
--   Restating the second law in terms of @'join'@:
--
--   * @'liftIO' '.' 'join' = 'join' '.' 'fmap' 'liftIO' '.' 'liftIO'@
--
--   The left monad action laws can now be easily proved using string diagrams.
--   Functors compose vertically, natural transformations from left to right,
--   @───@ represents @m@, @┈┈┈@ represents @'IO'@, @├@ represents @'return'@ or
--   @'join'@ depending on the number of inputs, and @┈┈┈►───@ represents @'liftIO'@.
--   The @'MonadIO'@ laws as string diagrams are:
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
--   >    ├┈┈┈►──┐          ├──────┐
--   >           ├──  =            ├──  =  ──────
--   > ──────────┘       ──────────┘
--
--   In other words,
--
--   @   'lact' '.' 'return'
--   = 'join' '.' 'liftIO' '.' 'return'
--   = 'join' '.' 'return'
--   = 'id'@
--
--   To prove associativity:
--
--   > ┈┈┈┐                ┈┈►──┐              ┈────┈─►─┐
--   >    ├┈┈►─┐                ├──┐           ┈┈►──┐   ├───
--   > ┈┈┈┘    ├──────  =  ┈┈►──┘  ├──────  =       ├───┘
--   > ────────┘           ────────┘           ─────┘
--
--   In other words,
--
--   @  'lact' '.' 'join'
--   = 'join' '.' 'liftIO' '.' 'join'
--   = 'join' '.' 'join' '.' 'fmap' 'liftIO' '.' 'liftIO'
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' 'liftIO' '.' 'liftIO'
--   = 'join' '.' 'fmap' ('join' '.' 'liftIO') '.' 'liftIO'
--   = 'join' '.' 'liftIO' '.' 'fmap' ('join' '.' 'liftIO')
--   = 'lact' '.' 'fmap' 'lact'@
instance (MonadIO m) => LeftModule IO m where
  lact = join . liftIO
