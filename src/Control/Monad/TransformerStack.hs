{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.TransformerStack (LiftBy, Steps, Nat (..), LiftStack (..)) where

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

-- | All @'LiftStack'@ instances are defined inductively using @'Control.Monad.Trans.Class.MonadTrans'@.
--   @'Control.Monad.Trans.Class.MonadTrans'@ instances are required to satisfy these laws, which state
--   that @'Control.Monad.Trans.Class.lift'@ is a monad homomorphism:
--
--   * @'Control.Monad.Trans.Class.lift' '.' 'pure' = 'pure'@
--
--   * @'Control.Monad.Trans.Class.lift' (m '>>=' f) = 'Control.Monad.Trans.Class.lift' m '>>=' ('Control.Monad.Trans.Class.lift' '.' f)@
--
--   Restating the second law in terms of @'join'@:
--
--   * @'Control.Monad.Trans.Class.lift' '.' 'join' = 'join' '.' 'fmap' 'Control.Monad.Trans.Class.lift' '.' 'Control.Monad.Trans.Class.lift'@
--
--   Because the composition of two monad homomorphisms is a monad homomorphism, @'liftStack'@ also satisfies these laws:
--
--   * @'liftStack' '.' 'pure' = 'pure'@
--
--   * @'liftStack' '.' 'join' = 'join' '.' 'fmap' 'liftStack' '.' 'liftStack'@
--
--   The left monad action laws can now be easily proved using string diagrams.
--   Functors compose from top to bottom, natural transformations from left to right,
--   @───@ represents @t m@, @┈┈┈@ represents @m@, @├@ represents @'pure'@ or
--   @'join'@ depending on the number of inputs, and @┈┈┈►───@ represents @'liftStack'@.
--   The @'LiftStack'@ laws as string diagrams are:
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
--   = 'join' '.' 'liftStack' '.' 'pure'
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
--   = 'join' '.' 'liftStack' '.' 'join'
--   = 'join' '.' 'join' '.' 'fmap' 'liftStack' '.' 'liftStack'
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' 'liftStack' '.' 'liftStack'
--   = 'join' '.' 'fmap' ('join' '.' 'liftStack') '.' 'liftStack'
--   = 'join' '.' 'liftStack' '.' 'fmap' ('join' '.' 'liftStack')
--   = 'ljoin' '.' 'fmap' 'ljoin'@
--
--   We can prove the right module laws using string diagrams in the same way.
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
--   = 'join' '.' 'fmap' 'liftStack' , 'pure'
--   = 'join' '.' 'fmap' 'liftStack' , 'fmap' 'pure'
--   = 'join' '.' 'fmap' ('liftStack' , 'pure')
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
--   = 'join' '.' 'fmap' 'liftStack' '.' 'fmap' 'join'
--   = 'join' '.' 'fmap' ('liftStack' '.' 'join')
--   = 'join' '.' 'fmap' ('join' '.' 'fmap' 'liftStack' '.' 'liftStack')
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' ('fmap' 'liftStack' '.' 'liftStack')
--   = 'join' '.' 'join' '.' 'fmap' ('fmap' 'liftStack') '.' 'fmap' ('liftStack')
--   = 'join' '.' 'fmap' 'liftStack' '.' 'join' '.' 'fmap' 'liftStack'
--   = 'rjoin' '.' 'rjoin'@
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
--   @  'bijoin'
--   = 'join' '.' 'join' '.' 'liftStack' '.' 'fmap' ('fmap' 'liftStack')
--   = 'join' '.' 'fmap' 'liftStack' '.' 'join' '.' 'liftStack'
--   = 'rjoin' '.' 'ljoin'
--   = 'join' '.' 'fmap' 'liftStack' '.' 'join' '.' 'liftStack'
--   = 'join' '.' 'fmap' 'join' '.' 'fmap' ('fmap' 'liftStack') '.' 'liftStack'
--   = 'join' '.' 'fmap' ('join' '.' 'fmap' 'liftStack') '.' 'liftStack'
--   = 'join' '.' 'fmap' 'rjoin' '.' 'liftStack'
--   = 'join' '.' 'liftStack' '.' 'fmap' 'rjoin'
--   = 'ljoin' '.' 'fmap' 'rjoin'@
class (LiftBy (Steps m n) m n) => LiftStack m n where
  liftStack :: forall a. m a -> n a

instance (LiftBy (Steps m n) m n) => LiftStack m n where
  liftStack = liftBy @(Steps m n)
