{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.TransformerStack
  ( MonadTransStack (..),
    IsState (..),
    IsWriter (..),
    IsRWS (..),
    IsReader (..),
    rws,
  )
where

import Control.Monad.Accum ()
import Control.Monad.Action.TH
import Control.Monad.Co ()
import Control.Monad.RWS.CPS qualified as CPSRWS (RWS, runRWS)
import Control.Monad.RWS.Class (MonadRWS, MonadReader (..), MonadWriter (..))
import Control.Monad.RWS.Lazy qualified as LazyRWS (RWS, runRWS)
import Control.Monad.RWS.Strict qualified as StrictRWS (RWS, runRWS)
import Control.Monad.Reader qualified as Reader
import Control.Monad.State.Class (MonadState (..))
import Control.Monad.State.Lazy qualified as LazyState (State, runState)
import Control.Monad.State.Strict qualified as StrictState (State, runState)
import Control.Monad.Trans ()
import Control.Monad.Trans.Accum ()
import Control.Monad.Trans.Compose ()
import Control.Monad.Trans.Except ()
import Control.Monad.Trans.Free ()
import Control.Monad.Trans.Iter ()
import Control.Monad.Trans.Maybe ()
import Control.Monad.Trans.RWS ()
import Control.Monad.Trans.RWS.CPS ()
import Control.Monad.Trans.RWS.Lazy ()
import Control.Monad.Trans.RWS.Strict ()
import Control.Monad.Trans.Reader ()
import Control.Monad.Trans.Select ()
import Control.Monad.Trans.State.Lazy ()
import Control.Monad.Trans.State.Strict ()
import Control.Monad.Trans.Writer ()
import Control.Monad.Trans.Writer.CPS ()
import Control.Monad.Trans.Writer.Lazy ()
import Control.Monad.Trans.Writer.Strict ()
import Control.Monad.Writer.CPS qualified as CPSWriter (Writer, runWriter)
import Control.Monad.Writer.Class ()
import Control.Monad.Writer.Lazy qualified as LazyWriter (Writer, runWriter)
import Control.Monad.Writer.Strict qualified as StrictWriter (Writer, runWriter)
import Data.Tuple (swap)

$mkLiftBy

-- | @'MonadTransStack' m n@ means that @n@ is a stack of monad transformers over @m@.
--
--   All @'MonadTransStack'@ instances are defined inductively using @'Control.Monad.Trans.Class.MonadTrans'@.
--   @'Control.Monad.Trans.Class.MonadTrans'@ instances are required to satisfy these laws, which state
--   that @'Control.Monad.Trans.Class.lift'@ is a monad homomorphism:
--
--   * @'Control.Monad.Trans.Class.lift' '.' 'pure' = 'pure'@
--
--   * @'Control.Monad.Trans.Class.lift' (m '>>=' f) = 'Control.Monad.Trans.Class.lift' m '>>=' ('Control.Monad.Trans.Class.lift' '.' f)@
--
--   Restating the second law in terms of @'Control.Monad.join'@:
--
--   * @'Control.Monad.Trans.Class.lift' '.' 'Control.Monad.join' = 'Control.Monad.join' '.' 'fmap' 'Control.Monad.Trans.Class.lift' '.' 'Control.Monad.Trans.Class.lift'@
--
--   Because the composition of two monad homomorphisms is a monad homomorphism, @'liftStack'@ also satisfies these laws:
--
--   * @'liftStack' '.' 'pure' = 'pure'@
--
--   * @'liftStack' '.' 'Control.Monad.join' = 'Control.Monad.join' '.' 'fmap' 'liftStack' '.' 'liftStack'@
--
--   The left monad action laws can now be easily proved using string diagrams.
--   Functors compose from top to bottom, natural transformations from left to right,
--   @───@ represents @t m@, @┈┈┈@ represents @m@, @├@ represents @'pure'@ or
--   @'Control.Monad.join'@ depending on the number of inputs, and @┈┈┈►───@ represents @'liftStack'@.
--   The @'MonadTransStack'@ laws as string diagrams are:
--
--   > ├┈┈┈►───  = ├──────
--
--   > ┈┈┈┐            ┈┈┈►───┐
--   >    ├┈┈┈►───  =         ├───
--   > ┈┈┈┘            ┈┈┈►───┘
--
--   and the diagram for @'Control.Monad.Action.ljoin'@ is:
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
--   Or in Haskell notation:
--
--   @   'Control.Monad.Action.ljoin' '.' 'pure'
--   = 'Control.Monad.join' '.' 'liftStack' '.' 'pure'
--   = 'Control.Monad.join' '.' 'pure'
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
--   Or in Haskell notation:
--
--   @  'Control.Monad.Action.ljoin' '.' 'Control.Monad.join'
--   = 'Control.Monad.join' '.' 'liftStack' '.' 'Control.Monad.join'
--   = 'Control.Monad.join' '.' 'Control.Monad.join' '.' 'fmap' 'liftStack' '.' 'liftStack'
--   = 'Control.Monad.join' '.' 'fmap' 'Control.Monad.join' '.' 'fmap' 'liftStack' '.' 'liftStack'
--   = 'Control.Monad.join' '.' 'fmap' ('Control.Monad.join' '.' 'liftStack') '.' 'liftStack'
--   = 'Control.Monad.join' '.' 'liftStack' '.' 'fmap' ('Control.Monad.join' '.' 'liftStack')
--   = 'Control.Monad.Action.ljoin' '.' 'fmap' 'Control.Monad.Action.ljoin'@
--
--   We can prove the right module laws using string diagrams in the same way.
--
--   The diagram for @'Control.Monad.Action.rjoin'@ is:
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
--   Or in Haskell notation:
--
--   @   'Control.Monad.Action.rjoin' '.' 'fmap' 'pure'
--   = 'Control.Monad.join' '.' 'fmap' 'liftStack' , 'pure'
--   = 'Control.Monad.join' '.' 'fmap' 'liftStack' , 'fmap' 'pure'
--   = 'Control.Monad.join' '.' 'fmap' ('liftStack' , 'pure')
--   = 'Control.Monad.join' '.' 'fmap' 'pure'
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
--   Or in Haskell notation:
--
--   @  'Control.Monad.Action.rjoin' '.' 'fmap' 'Control.Monad.join'
--   = 'Control.Monad.join' '.' 'fmap' 'liftStack' '.' 'fmap' 'Control.Monad.join'
--   = 'Control.Monad.join' '.' 'fmap' ('liftStack' '.' 'Control.Monad.join')
--   = 'Control.Monad.join' '.' 'fmap' ('Control.Monad.join' '.' 'fmap' 'liftStack' '.' 'liftStack')
--   = 'Control.Monad.join' '.' 'fmap' 'Control.Monad.join' '.' 'fmap' ('fmap' 'liftStack' '.' 'liftStack')
--   = 'Control.Monad.join' '.' 'Control.Monad.join' '.' 'fmap' ('fmap' 'liftStack') '.' 'fmap' ('liftStack')
--   = 'Control.Monad.join' '.' 'fmap' 'liftStack' '.' 'Control.Monad.join' '.' 'fmap' 'liftStack'
--   = 'Control.Monad.Action.rjoin' '.' 'Control.Monad.Action.rjoin'@
--
--   The bimodule law can be proved as follows:
--
--   > ┈┈┈►─┐             ┈┈►─┐
--   >      ├───┐             ├───┐          ┈┈┈┈┈┈►─┐
--   > ─────┘   ├────  =  ────┘   ├────  =   ────┐   ├────
--   > ┈►───────┘         ┈┈┈┈┈┈►─┘              ├───┘
--   >                                       ┈┈►─┘
--
--   Or in Haskell notation:
--
--   @  'Control.Monad.Action.bijoin'
--   = 'Control.Monad.join' '.' 'Control.Monad.join' '.' 'liftStack' '.' 'fmap' ('fmap' 'liftStack')
--   = 'Control.Monad.join' '.' 'fmap' 'liftStack' '.' 'Control.Monad.join' '.' 'liftStack'
--   = 'Control.Monad.Action.rjoin' '.' 'Control.Monad.Action.ljoin'
--   = 'Control.Monad.join' '.' 'fmap' 'liftStack' '.' 'Control.Monad.join' '.' 'liftStack'
--   = 'Control.Monad.join' '.' 'fmap' 'Control.Monad.join' '.' 'fmap' ('fmap' 'liftStack') '.' 'liftStack'
--   = 'Control.Monad.join' '.' 'fmap' ('Control.Monad.join' '.' 'fmap' 'liftStack') '.' 'liftStack'
--   = 'Control.Monad.join' '.' 'fmap' 'Control.Monad.Action.rjoin' '.' 'liftStack'
--   = 'Control.Monad.join' '.' 'liftStack' '.' 'fmap' 'Control.Monad.Action.rjoin'
--   = 'Control.Monad.Action.ljoin' '.' 'fmap' 'Control.Monad.Action.rjoin'@
class (LiftBy (Steps m n) m n) => MonadTransStack m n where
  liftStack :: forall a. m a -> n a

instance (LiftBy (Steps m n) m n) => MonadTransStack m n where
  liftStack = liftBy @(Steps m n)

-- | @'IsReader' r m@ means that @m@ is an implementation of the reader monad, or, in other words, @'reader'@ is a monad isomorphism whose inverse is @'runReader'@.
class (MonadReader r m) => IsReader r m where
  runReader :: forall a. m a -> r -> a

instance IsReader r ((->) r) where
  runReader = id

instance IsReader r (Reader.Reader r) where
  runReader = Reader.runReader

-- | @'IsState' s m@ means that @m@ is an implementation of the state monad, or, in other words, @'state'@ is a monad isomorphism whose inverse is @'runState'@.
class (MonadState s m) => IsState s m where
  runState :: forall a. m a -> s -> (a, s)

instance IsState s (LazyState.State s) where
  runState = LazyState.runState

instance IsState s (StrictState.State s) where
  runState = StrictState.runState

-- | @'IsWriter' w m@ means that @m@ is an implementation of the writer monad, or, in other words, @'writer'@ is a monad isomorphism whose inverse is @'runWriter'@.
class (MonadWriter w m) => IsWriter w m where
  runWriter :: forall a. m a -> (a, w)

instance (Monoid w) => IsWriter w ((,) w) where
  runWriter = swap

instance (Monoid w) => IsWriter w (LazyWriter.Writer w) where
  runWriter = LazyWriter.runWriter

instance (Monoid w) => IsWriter w (StrictWriter.Writer w) where
  runWriter = StrictWriter.runWriter

instance (Monoid w) => IsWriter w (CPSWriter.Writer w) where
  runWriter = CPSWriter.runWriter

-- | @'IsRWS' r w s m@ means that @m@ is an implementation of the rws monad, or, in other words, @'rws'@ is a monad isomorphism whose inverse is @'runRWS'@.
class (MonadRWS r w s m) => IsRWS r w s m where
  runRWS :: forall a. m a -> r -> s -> (a, s, w)

instance (Monoid w) => IsRWS r w s (LazyRWS.RWS r w s) where
  runRWS = LazyRWS.runRWS

instance (Monoid w) => IsRWS r w s (StrictRWS.RWS r w s) where
  runRWS = StrictRWS.runRWS

instance (Monoid w) => IsRWS r w s (CPSRWS.RWS r w s) where
  runRWS = CPSRWS.runRWS

rws :: (MonadRWS r w s m) => (r -> s -> (a, s, w)) -> m a
rws f =
  ask >>= \r ->
    get >>= \s ->
      let (a, s', w) = f r s
       in put s'
            >> tell w
            >> pure a
