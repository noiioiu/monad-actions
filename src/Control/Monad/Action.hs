{-# LANGUAGE IncoherentInstances #-}

-- | A monad action is a monoid action in the category of endofunctors, what's the problem?
module Control.Monad.Action
  ( LeftModule (..),
    RightModule (..),
    BiModule (..),
    monadTransLScale,
    monadTransRScale,
    monadTransBiScale,
  )
where

import Control.Monad (join)
import Control.Monad.Identity (Identity (..), IdentityT)
import Control.Monad.RWS.Lazy qualified as L
import Control.Monad.RWS.Strict qualified as S
import Control.Monad.Trans (MonadTrans (..))
import Control.Monad.Trans.Accum (AccumT)
import Control.Monad.Trans.Cont (ContT)
import Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Select (SelectT)
import Control.Monad.Trans.State.Lazy qualified as L
import Control.Monad.Trans.State.Strict qualified as S
import Control.Monad.Trans.Writer.CPS qualified as C
import Control.Monad.Trans.Writer.Lazy qualified as L
import Control.Monad.Trans.Writer.Strict qualified as S
import Data.Functor.Compose (Compose (..))
import Data.Maybe (catMaybes)

-- | Instances must satisfy the following laws:
--
-- * @'ljoin' '.' 'join' = 'ljoin' '.' 'fmap' 'ljoin'@
--
-- * @'ljoin' '.' 'pure' = 'id'@
class (Monad m, Functor f) => LeftModule m f where
  ljoin ::
    m (f a) ->
    -- | left monad action
    f a

-- | Instances must satisfy the following laws:
--
-- * @'rjoin' '.' 'fmap' 'join' = 'rjoin' '.' 'rjoin'@
--
-- * @'rjoin' '.' 'fmap' 'pure' = 'id'@
class (Monad m, Functor f) => RightModule m f where
  rjoin ::
    f (m a) ->
    -- | right monad action
    f a

-- | Given two monads r and s, an (r, s) bimodule is a functor that is a left module over r and a right module over s, where the two actions are compatible.
--   Instances must satisfy the following law in addition to the laws for @'LeftModule'@ and @'RightModule'@:
--
-- * @'rjoin' '.' 'ljoin' = 'ljoin' '.' 'fmap' 'rjoin' = 'bijoin'@
class (LeftModule r f, RightModule s f) => BiModule r s f where
  bijoin ::
    r (f (s a)) ->
    -- | two-sided monad action
    f a
  bijoin = rjoin . ljoin

instance (Monad m) => LeftModule m m where ljoin = join

instance (Monad m) => RightModule m m where rjoin = join

instance (Monad m) => BiModule m m m

instance (Functor f) => LeftModule Identity f where ljoin = runIdentity

instance (Functor f) => RightModule Identity f where rjoin = fmap runIdentity

instance (Functor f) => BiModule Identity Identity f

instance RightModule Maybe [] where rjoin = catMaybes

instance LeftModule Maybe [] where ljoin = concat

instance BiModule Maybe Maybe []

instance BiModule Maybe [] []

instance BiModule [] Maybe []

instance RightModule (Either e) Maybe where
  rjoin (Just (Right x)) = Just x
  rjoin _ = Nothing

instance LeftModule (Either e) Maybe where
  ljoin (Right (Just x)) = Just x
  ljoin _ = Nothing

instance BiModule (Either e) (Either f) Maybe

instance BiModule (Either e) Maybe Maybe

instance BiModule Maybe (Either f) Maybe

instance (Monad m, Functor f, LeftModule m n) => LeftModule m (Compose n f) where
  ljoin = Compose . ljoin . fmap getCompose

instance (Monad m, Functor f, RightModule m n) => RightModule m (Compose f n) where
  rjoin = Compose . fmap rjoin . getCompose

instance (Monad s, Monad t, Functor f, LeftModule s u, RightModule t v) => BiModule s t (Compose u (Compose f v))

-- | Default left scalar multiplication for monad transformers.
--
--   @'MonadTrans'@ instances are required to satisfy these laws, which state that @'lift'@ is a monad homomorphism:
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
--   and the diagram for @'ljoin'@ is:
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
--   @   'ljoin' '.' 'pure'
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
--   @  'ljoin' '.' 'join'
--   = 'join' '.' 'lift' '.' 'join'
--   = 'join' '.' 'join' '.' 'fmap' 'lift' '.' 'lift'
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' 'lift' '.' 'lift'
--   = 'join' '.' 'fmap' ('join' '.' 'lift') '.' 'lift'
--   = 'join' '.' 'lift' '.' 'fmap' ('join' '.' 'lift')
--   = 'ljoin' '.' 'fmap' 'ljoin'@
monadTransLScale :: (Monad m, MonadTrans t, Monad (t m)) => m (t m a) -> t m a
monadTransLScale = join . lift

instance (Monad m) => LeftModule m (MaybeT m) where ljoin = monadTransLScale

instance (Monad m) => LeftModule m (ExceptT e m) where ljoin = monadTransLScale

instance (Monad m) => LeftModule m (IdentityT m) where ljoin = monadTransLScale

instance (Monad m) => LeftModule m (ReaderT r m) where ljoin = monadTransLScale

instance (Monad m) => LeftModule m (SelectT r m) where ljoin = monadTransLScale

instance (Monad m) => LeftModule m (L.StateT r m) where ljoin = monadTransLScale

instance (Monad m) => LeftModule m (S.StateT r m) where ljoin = monadTransLScale

instance (Monad m) => LeftModule m (C.WriterT w m) where ljoin = monadTransLScale

instance (Monad m, Monoid w) => LeftModule m (S.WriterT w m) where ljoin = monadTransLScale

instance (Monad m, Monoid w) => LeftModule m (L.WriterT w m) where ljoin = monadTransLScale

instance (Monad m, Monoid w) => LeftModule m (AccumT w m) where ljoin = monadTransLScale

instance (Monad m) => LeftModule m (ContT r m) where ljoin = monadTransLScale

instance (Monad m, Monoid w) => LeftModule m (L.RWST r w s m) where ljoin = monadTransLScale

instance (Monad m, Monoid w) => LeftModule m (S.RWST r w s m) where ljoin = monadTransLScale

-- | Default right scalar multiplication for monad transformers.
--
--   We prove the right module laws using string diagrams, just as in the case
--   of the left module laws.
--
--   The diagram for @'rjoin'@ is:
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
--   @   'rjoin' '.' 'fmap' 'pure'
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
--   @  'rjoin' '.' 'fmap' 'join'
--   = 'join' '.' 'fmap' 'lift' '.' 'fmap' 'join'
--   = 'join' '.' 'fmap' ('lift' '.' 'join')
--   = 'join' '.' 'fmap' ('join' '.' 'fmap' 'lift' '.' 'lift')
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' ('fmap' 'lift' '.' 'lift')
--   = 'join' '.' 'join' '.' 'fmap' ('fmap' 'lift') '.' 'fmap' ('lift')
--   = 'join' '.' 'fmap' 'lift' '.' 'join' '.' 'fmap' 'lift'
--   = 'rjoin' '.' 'rjoin'@
monadTransRScale :: (Monad m, MonadTrans t, Monad (t m)) => t m (m a) -> t m a
monadTransRScale = (lift =<<)

instance (Monad m) => RightModule m (MaybeT m) where rjoin = monadTransRScale

instance (Monad m) => RightModule m (ExceptT e m) where rjoin = monadTransRScale

instance (Monad m) => RightModule m (IdentityT m) where rjoin = monadTransRScale

instance (Monad m) => RightModule m (ReaderT r m) where rjoin = monadTransRScale

instance (Monad m) => RightModule m (SelectT r m) where rjoin = monadTransRScale

instance (Monad m) => RightModule m (L.StateT r m) where rjoin = monadTransRScale

instance (Monad m) => RightModule m (S.StateT r m) where rjoin = monadTransRScale

instance (Monad m) => RightModule m (C.WriterT w m) where rjoin = monadTransRScale

instance (Monad m, Monoid w) => RightModule m (S.WriterT w m) where rjoin = monadTransRScale

instance (Monad m, Monoid w) => RightModule m (L.WriterT w m) where rjoin = monadTransRScale

instance (Monad m, Monoid w) => RightModule m (AccumT w m) where rjoin = monadTransRScale

instance (Monad m) => RightModule m (ContT r m) where rjoin = monadTransRScale

instance (Monad m, Monoid w) => RightModule m (L.RWST r w s m) where rjoin = monadTransRScale

instance (Monad m, Monoid w) => RightModule m (S.RWST r w s m) where rjoin = monadTransRScale

-- | Default two-sided scalar multiplication for monad transformers.
--
--   We prove the bimodule law using string diagrams, just as in the case
--   of the left and right module laws:
--
--   > ┈┈┈►─┐             ┈┈►─┐
--   >      ├───┐             ├───┐          ┈┈┈┈┈┈►─┐
--   > ─────┘   ├────  =  ────┘   ├────  =   ────┐   ├────
--   > ┈►───────┘         ┈┈┈┈┈┈►─┘              ├───┘
--   >                                       ┈┈►─┘
--
--   In other words,
--
--   @  'bijoin'
--   = 'join' '.' 'join' '.' 'lift' '.' 'fmap' ('fmap' 'lift')
--   = 'join' '.' 'fmap' 'lift' '.' 'join' '.' 'lift'
--   = 'rjoin' '.' 'ljoin'
--   = 'join' '.' 'fmap' 'lift' '.' 'join' '.' 'lift'
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' ('fmap' 'lift') '.' 'lift'
--   = 'join' '.' 'fmap' ('join' '.' 'fmap' 'lift') '.' 'lift'
--   = 'join' '.' 'fmap' 'rjoin' '.' 'lift'
--   = 'join' '.' 'lift' '.' 'fmap' 'rjoin'
--   = 'ljoin' '.' 'fmap' 'rjoin'@
monadTransBiScale :: (Monad m, MonadTrans t, Monad (t m)) => m (t m (m a)) -> t m a
monadTransBiScale = join . join . lift . fmap (fmap lift)

instance (Monad m) => BiModule m m (MaybeT m) where bijoin = monadTransBiScale

instance (Monad m) => BiModule m m (ExceptT e m) where bijoin = monadTransBiScale

instance (Monad m) => BiModule m m (IdentityT m) where bijoin = monadTransBiScale

instance (Monad m) => BiModule m m (ReaderT r m) where bijoin = monadTransBiScale

instance (Monad m) => BiModule m m (SelectT r m) where bijoin = monadTransBiScale

instance (Monad m) => BiModule m m (L.StateT r m) where bijoin = monadTransBiScale

instance (Monad m) => BiModule m m (S.StateT r m) where bijoin = monadTransBiScale

instance (Monad m) => BiModule m m (C.WriterT w m) where bijoin = monadTransBiScale

instance (Monad m, Monoid w) => BiModule m m (S.WriterT w m) where bijoin = monadTransBiScale

instance (Monad m, Monoid w) => BiModule m m (L.WriterT w m) where bijoin = monadTransBiScale

instance (Monad m, Monoid w) => BiModule m m (AccumT w m) where bijoin = monadTransBiScale

instance (Monad m) => BiModule m m (ContT r m) where bijoin = monadTransBiScale

instance (Monad m, Monoid w) => BiModule m m (L.RWST r w s m) where bijoin = monadTransBiScale

instance (Monad m, Monoid w) => BiModule m m (S.RWST r w s m) where bijoin = monadTransBiScale

-------------------------------------------------------

instance (Monad m) => LeftModule Maybe (MaybeT m) where
  ljoin = join . MaybeT . pure

instance (Monad m) => RightModule Maybe (MaybeT m) where
  rjoin = MaybeT . fmap join . runMaybeT

instance (Monad m) => LeftModule (Either e) (MaybeT m) where
  ljoin = join . MaybeT . fmap (either (const Nothing) Just) . pure @m

instance (Monad m) => RightModule (Either e) (MaybeT m) where
  rjoin = MaybeT . fmap (either (const Nothing) Just =<<) . runMaybeT

instance (Monoid e, Monad m) => LeftModule Maybe (ExceptT e m) where
  ljoin = join . ExceptT . pure . maybe (Left mempty) Right

instance (Monoid e, Monad m) => RightModule Maybe (ExceptT e m) where
  rjoin = ExceptT . fmap (maybe (Left mempty) Right =<<) . runExceptT

instance (Monad m) => LeftModule (Either e) (ExceptT e m) where
  ljoin = join . ExceptT . pure

instance (Monoid e, Monad m) => RightModule (Either e) (ExceptT e m) where
  rjoin = ExceptT . fmap join . runExceptT

instance (Monad m) => BiModule Maybe Maybe (MaybeT m)

instance (Monad m) => BiModule (Either e) Maybe (MaybeT m)

instance (Monad m) => BiModule Maybe (Either e) (MaybeT m)

instance (Monad m) => BiModule (Either e) (Either f) (MaybeT m)

instance (Monoid e, Monad m) => BiModule Maybe Maybe (ExceptT e m)

instance (Monoid e, Monad m) => BiModule (Either e) Maybe (ExceptT e m)

instance (Monoid e, Monad m) => BiModule Maybe (Either e) (ExceptT e m)

instance (Monoid e, Monad m) => BiModule (Either e) (Either e) (ExceptT e m)
