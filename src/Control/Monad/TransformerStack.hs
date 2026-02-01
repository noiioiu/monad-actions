{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.TransformerStack (MonadTransStack (..)) where

import Control.Monad.Action.TH
import Control.Monad.Co ()
import Control.Monad.Trans ()
import Control.Monad.Trans.Accum ()
import Control.Monad.Trans.Compose ()
import Control.Monad.Trans.Except ()
import Control.Monad.Trans.Free ()
import Control.Monad.Trans.Iter ()
import Control.Monad.Trans.Maybe ()
import Control.Monad.Trans.Reader ()
import Control.Monad.Trans.Select ()
import Control.Monad.Trans.State.Lazy qualified as L ()
import Control.Monad.Trans.State.Strict qualified as S ()
import Control.Monad.Trans.Writer ()
import Control.Monad.Trans.Writer.CPS qualified as C ()
import Control.Monad.Trans.Writer.Lazy qualified as L ()
import Control.Monad.Trans.Writer.Strict qualified as S ()

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
--   In other words,
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
--   In other words,
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
--   In other words,
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
--   In other words,
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
--   In other words,
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
