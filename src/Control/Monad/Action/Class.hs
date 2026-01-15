module Control.Monad.Action.Class
  ( LeftModule (..),
    RightModule (..),
    BiModule (..),
    monadTransLScale,
    monadTransRScale,
    monadTransBiScale,
  )
where

import Control.Monad (join)
import Control.Monad.Morph

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
  ljoin = (`lbind` id)
  lbind :: m a -> (a -> f b) -> f b
  lbind = (ljoin .) . flip fmap

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
  rjoin = (`rbind` id)
  rbind :: f a -> (a -> m b) -> f b
  rbind = (rjoin .) . flip fmap

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
