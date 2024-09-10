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
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Select (SelectT)
import Control.Monad.Trans.State.Lazy qualified as L
import Control.Monad.Trans.State.Strict qualified as S
import Control.Monad.Trans.Writer.CPS qualified as C
import Control.Monad.Trans.Writer.Lazy qualified as L
import Control.Monad.Trans.Writer.Strict qualified as S
import Data.Functor.Compose
import Data.Maybe (catMaybes)

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

instance (Monad m) => LeftModule m m where lact = join

instance (Monad m) => RightModule m m where ract = join

instance (Monad m) => BiModule m m m

instance (Functor f) => LeftModule Identity f where lact = runIdentity

instance (Functor f) => RightModule Identity f where ract = fmap runIdentity

instance (Functor f) => BiModule Identity Identity f

instance RightModule Maybe [] where ract = catMaybes

instance LeftModule Maybe [] where lact = concat

instance BiModule Maybe Maybe []

instance BiModule Maybe [] []

instance BiModule [] Maybe []

instance RightModule (Either e) Maybe where
  ract (Just (Right x)) = Just x
  ract _ = Nothing

instance LeftModule (Either e) Maybe where
  lact (Right (Just x)) = Just x
  lact _ = Nothing

instance BiModule (Either e) (Either f) Maybe

instance BiModule (Either e) Maybe Maybe

instance BiModule Maybe (Either f) Maybe

instance (Monad m, Functor f, LeftModule m n) => LeftModule m (Compose n f) where
  lact = Compose . lact . fmap getCompose

instance (Monad m, Functor f, RightModule m n) => RightModule m (Compose f n) where
  ract = Compose . fmap ract . getCompose

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
monadTransLScale :: (Monad m, MonadTrans t, Monad (t m)) => m (t m a) -> t m a
monadTransLScale = join . lift

instance (Monad m) => LeftModule m (MaybeT m) where lact = monadTransLScale

instance (Monad m) => LeftModule m (ExceptT e m) where lact = monadTransLScale

instance (Monad m) => LeftModule m (IdentityT m) where lact = monadTransLScale

instance (Monad m) => LeftModule m (ReaderT r m) where lact = monadTransLScale

instance (Monad m) => LeftModule m (SelectT r m) where lact = monadTransLScale

instance (Monad m) => LeftModule m (L.StateT r m) where lact = monadTransLScale

instance (Monad m) => LeftModule m (S.StateT r m) where lact = monadTransLScale

instance (Monad m) => LeftModule m (C.WriterT w m) where lact = monadTransLScale

instance (Monad m, Monoid w) => LeftModule m (S.WriterT w m) where lact = monadTransLScale

instance (Monad m, Monoid w) => LeftModule m (L.WriterT w m) where lact = monadTransLScale

instance (Monad m, Monoid w) => LeftModule m (AccumT w m) where lact = monadTransLScale

instance (Monad m) => LeftModule m (ContT r m) where lact = monadTransLScale

instance (Monad m, Monoid w) => LeftModule m (L.RWST r w s m) where lact = monadTransLScale

instance (Monad m, Monoid w) => LeftModule m (S.RWST r w s m) where lact = monadTransLScale

-- | Default right scalar multiplication for monad transformers.
--
--   We prove the right module laws using string diagrams, just as in the case
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
monadTransRScale :: (Monad m, MonadTrans t, Monad (t m)) => t m (m a) -> t m a
monadTransRScale = (lift =<<)

instance (Monad m) => RightModule m (MaybeT m) where ract = monadTransRScale

instance (Monad m) => RightModule m (ExceptT e m) where ract = monadTransRScale

instance (Monad m) => RightModule m (IdentityT m) where ract = monadTransRScale

instance (Monad m) => RightModule m (ReaderT r m) where ract = monadTransRScale

instance (Monad m) => RightModule m (SelectT r m) where ract = monadTransRScale

instance (Monad m) => RightModule m (L.StateT r m) where ract = monadTransRScale

instance (Monad m) => RightModule m (S.StateT r m) where ract = monadTransRScale

instance (Monad m) => RightModule m (C.WriterT w m) where ract = monadTransRScale

instance (Monad m, Monoid w) => RightModule m (S.WriterT w m) where ract = monadTransRScale

instance (Monad m, Monoid w) => RightModule m (L.WriterT w m) where ract = monadTransRScale

instance (Monad m, Monoid w) => RightModule m (AccumT w m) where ract = monadTransRScale

instance (Monad m) => RightModule m (ContT r m) where ract = monadTransRScale

instance (Monad m, Monoid w) => RightModule m (L.RWST r w s m) where ract = monadTransRScale

instance (Monad m, Monoid w) => RightModule m (S.RWST r w s m) where ract = monadTransRScale

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
--   @  'biact'
--   = 'join' '.' 'join' '.' 'lift' '.' 'fmap' ('fmap' 'lift')
--   = 'join' '.' 'fmap' 'lift' '.' 'join' '.' 'lift'
--   = 'ract' '.' 'lact'
--   = 'join' '.' 'fmap' 'lift' '.' 'join' '.' 'lift'
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' ('fmap' 'lift') '.' 'lift'
--   = 'join' '.' 'fmap' ('join' '.' 'fmap' 'lift') '.' 'lift'
--   = 'join' '.' 'fmap' 'ract' '.' 'lift'
--   = 'join' '.' 'lift' '.' 'fmap' 'ract'
--   = 'lact' '.' 'fmap' 'ract'@
monadTransBiScale :: (Monad m, MonadTrans t, Monad (t m)) => m (t m (m a)) -> t m a
monadTransBiScale = join . join . lift . fmap (fmap lift)

instance (Monad m) => BiModule m m (MaybeT m) where biact = monadTransBiScale

instance (Monad m) => BiModule m m (ExceptT e m) where biact = monadTransBiScale

instance (Monad m) => BiModule m m (IdentityT m) where biact = monadTransBiScale

instance (Monad m) => BiModule m m (ReaderT r m) where biact = monadTransBiScale

instance (Monad m) => BiModule m m (SelectT r m) where biact = monadTransBiScale

instance (Monad m) => BiModule m m (L.StateT r m) where biact = monadTransBiScale

instance (Monad m) => BiModule m m (S.StateT r m) where biact = monadTransBiScale

instance (Monad m) => BiModule m m (C.WriterT w m) where biact = monadTransBiScale

instance (Monad m, Monoid w) => BiModule m m (S.WriterT w m) where biact = monadTransBiScale

instance (Monad m, Monoid w) => BiModule m m (L.WriterT w m) where biact = monadTransBiScale

instance (Monad m, Monoid w) => BiModule m m (AccumT w m) where biact = monadTransBiScale

instance (Monad m) => BiModule m m (ContT r m) where biact = monadTransBiScale

instance (Monad m, Monoid w) => BiModule m m (L.RWST r w s m) where biact = monadTransBiScale

instance (Monad m, Monoid w) => BiModule m m (S.RWST r w s m) where biact = monadTransBiScale
