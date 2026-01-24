{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Given a monad \(M\) on a category \(\mathcal{D}\) with unit \(\eta\) and
--     multiplication \(\mu\) and a functor \(F\) from \(\mathcal{C}\) to \(\mathcal{D}\),
--     a left monad action of \(M\) on \(F\) is a natural transformation \(\nu: M \circ F \to F\)
--     such that the following two laws hold:
--
--     * \(\nu \cdot (\eta \circ F) = \mathrm{id}_F\)
--     * \(\nu \cdot (\mu \circ F) = \nu \cdot (M \circ \nu)\)
--
--     We also say that \(F\) is a left module over \(M\).  In the case
--     \(\mathcal{C} = \mathcal{D}\), a left monad module is a left monoid module
--     object in the category of endofunctors on \(\mathcal{C}\).  We may also
--     call \(\alpha\) the scalar multiplication of the module by the monad, by analogy
--     with ring modules, which are monoid module objects in the category of abelian groups
--     with tensor product as the monoidal product (rings are just monoid objects in this
--     category).
--
--     Right monad actions are defined similarly.
--
--     See [this blog post](https://stringdiagram.com/2023/04/23/monad-actions/) by Dan Marsden
--     or the paper /Modules over monads and their algebras/ by Piróg, Wu, and Gibbons.
module Control.Monad.Action
  ( LeftModule (..),
    RightModule (..),
    BiModule (..),
  )
where

import Control.Monad (join)
import Control.Monad.Action.TH
import Control.Monad.Co ()
import Control.Monad.Codensity (Codensity (..))
import Control.Monad.Error.Class (MonadError (..), liftEither)
import Control.Monad.IO.Class
import Control.Monad.Identity (Identity (..))
import Control.Monad.Reader.Class (MonadReader (..))
import Control.Monad.State (MonadState (..), State, runState)
import Control.Monad.State.Class (MonadState, gets)
import Control.Monad.Trans ()
import Control.Monad.Trans.Accum ()
import Control.Monad.Trans.Compose ()
import Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import Control.Monad.Trans.Free ()
import Control.Monad.Trans.Iter ()
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.Reader ()
import Control.Monad.Trans.Select ()
import Control.Monad.Trans.State.Lazy qualified as L ()
import Control.Monad.Trans.State.Strict qualified as S ()
import Control.Monad.Trans.Writer.CPS qualified as C ()
import Control.Monad.Trans.Writer.Lazy qualified as L ()
import Control.Monad.Trans.Writer.Strict qualified as S ()
import Data.Functor.Compose (Compose (..))
import Data.List.NonEmpty qualified as NE (NonEmpty, toList)
import Data.Maybe (catMaybes, mapMaybe)

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
  {-# MINIMAL ljoin | lbind #-}

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
  {-# MINIMAL rjoin | rbind #-}

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

-- | All @'LiftStack'@ instances are defined inductively using @'MonadTrans'@.
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
class LiftStack m n where
  liftStack :: forall a. m a -> n a

$mkLiftStackInstances

instance {-# OVERLAPS #-} (Monad n, Monad m, LiftStack m n) => LeftModule m n where
  ljoin = join . liftStack
  lbind = (>>=) . liftStack

instance {-# OVERLAPS #-} (Monad n, Monad m, LiftStack m n) => RightModule m n where
  rjoin = join . fmap liftStack
  rbind = flip $ flip (>>=) . (liftStack .)

instance {-# OVERLAPS #-} (Monad n, Monad m, LiftStack m n) => BiModule m m n

instance {-# INCOHERENT #-} (Functor f) => LeftModule Identity f where ljoin = runIdentity

instance {-# INCOHERENT #-} (Functor f) => RightModule Identity f where rjoin = fmap runIdentity

instance {-# INCOHERENT #-} (Functor f) => BiModule Identity Identity f

instance {-# INCOHERENT #-} RightModule Maybe [] where rjoin = catMaybes; rbind = flip mapMaybe

instance {-# INCOHERENT #-} LeftModule Maybe [] where ljoin = concat; lbind = flip concatMap

instance {-# INCOHERENT #-} LeftModule NE.NonEmpty [] where ljoin = concat; lbind = flip concatMap

instance {-# INCOHERENT #-} RightModule NE.NonEmpty [] where rjoin = (>>= NE.toList)

instance {-# INCOHERENT #-} BiModule Maybe Maybe []

instance {-# INCOHERENT #-} BiModule Maybe [] []

instance BiModule [] Maybe []

instance {-# INCOHERENT #-} BiModule NE.NonEmpty NE.NonEmpty []

instance BiModule [] NE.NonEmpty []

instance BiModule NE.NonEmpty [] []

instance BiModule Maybe NE.NonEmpty []

instance BiModule NE.NonEmpty Maybe []

instance {-# INCOHERENT #-} RightModule (Either e) Maybe where
  rjoin (Just (Right x)) = Just x
  rjoin _ = Nothing

instance {-# INCOHERENT #-} LeftModule (Either e) Maybe where
  ljoin (Right (Just x)) = Just x
  ljoin _ = Nothing

instance BiModule (Either e) (Either f) Maybe

instance BiModule (Either e) Maybe Maybe

instance BiModule Maybe (Either f) Maybe

instance {-# INCOHERENT #-} (Monad m, Functor f, LeftModule m n) => LeftModule m (Compose n f) where
  ljoin = Compose . ljoin . fmap getCompose
  a `lbind` f = Compose $ a `lbind` (getCompose . f)

instance {-# INCOHERENT #-} (Monad m, Functor f, RightModule m n) => RightModule m (Compose f n) where
  rjoin = Compose . fmap rjoin . getCompose
  a `rbind` f = Compose . fmap (`rbind` f) $ getCompose a

instance {-# INCOHERENT #-} (Monad s, Monad t, Functor f, LeftModule s u, RightModule t v) => BiModule s t (Compose u (Compose f v))

instance {-# INCOHERENT #-} (Monad m) => LeftModule Maybe (MaybeT m) where
  ljoin = join . MaybeT . pure

instance {-# INCOHERENT #-} (Monad m) => RightModule Maybe (MaybeT m) where
  rjoin = MaybeT . fmap join . runMaybeT

instance {-# INCOHERENT #-} (Monad m) => LeftModule (Either e) (MaybeT m) where
  ljoin = join . MaybeT . fmap (either (const Nothing) Just) . pure @m

instance {-# INCOHERENT #-} (Monad m) => RightModule (Either e) (MaybeT m) where
  rjoin = MaybeT . fmap (either (const Nothing) Just =<<) . runMaybeT

instance {-# INCOHERENT #-} (Monoid e, Monad m) => LeftModule Maybe (ExceptT e m) where
  ljoin = join . ExceptT . pure . maybe (Left mempty) Right

instance {-# INCOHERENT #-} (Monoid e, Monad m) => RightModule Maybe (ExceptT e m) where
  rjoin = ExceptT . fmap (maybe (Left mempty) Right =<<) . runExceptT

instance {-# INCOHERENT #-} (Monad m) => BiModule Maybe Maybe (MaybeT m)

instance {-# INCOHERENT #-} (Monad m) => BiModule (Either e) Maybe (MaybeT m)

instance {-# INCOHERENT #-} (Monad m) => BiModule Maybe (Either e) (MaybeT m)

instance {-# INCOHERENT #-} (Monad m) => BiModule (Either e) (Either f) (MaybeT m)

instance {-# INCOHERENT #-} (Monoid e, Monad m) => BiModule Maybe Maybe (ExceptT e m)

instance {-# INCOHERENT #-} (Monoid e, Monad m) => BiModule (Either e) Maybe (ExceptT e m)

instance {-# INCOHERENT #-} (Monoid e, Monad m) => BiModule Maybe (Either e) (ExceptT e m)

-- | @'liftIO'@ is a monad homomorphism, so the proof that every monad with a lawful @'MonadIO'@
--   instance is a {left,right,bi} module over @'IO'@ is the same as the proof for monad transformers.
instance {-# INCOHERENT #-} (MonadIO m) => LeftModule IO m where
  ljoin = join . liftIO
  a `lbind` f = liftIO a >>= f

instance {-# INCOHERENT #-} (MonadIO m) => RightModule IO m where
  rjoin = (>>= liftIO)
  a `rbind` f = a >>= (liftIO . f)

instance {-# INCOHERENT #-} (MonadIO m) => BiModule IO IO m

-- | No laws are given in the documentation for @'MonadError'@, but we assume
--   @'liftEither'@ is a monad homomorphism.
instance {-# INCOHERENT #-} (MonadError e m) => LeftModule (Either e) m where
  ljoin = join . liftEither
  a `lbind` f = liftEither a >>= f

instance {-# INCOHERENT #-} (MonadError e m) => RightModule (Either e) m where
  rjoin = (>>= liftEither)
  a `rbind` f = a >>= (liftEither . f)

instance {-# INCOHERENT #-} (MonadError e m) => BiModule (Either e) (Either e) m

-- | For all lawful @'MonadReader'@ instances, @'reader'@ is a monad homomorphism.
instance {-# INCOHERENT #-} (MonadReader r m) => LeftModule ((->) r) m where
  ljoin = join . reader
  a `lbind` f = reader a >>= f

instance {-# INCOHERENT #-} (MonadReader r m) => RightModule ((->) r) m where
  rjoin = (>>= reader)
  a `rbind` f = a >>= (reader . f)

instance {-# INCOHERENT #-} (MonadReader r m) => BiModule ((->) r) ((->) r) m

-- | For all lawful @'MonadState'@ instances, @'state'@ is a monad homomorphism.
instance {-# INCOHERENT #-} (MonadState s m) => LeftModule (State s) m where
  ljoin = join . state . runState
  a `lbind` f = state (runState a) >>= f

instance {-# INCOHERENT #-} (MonadState s m) => RightModule (State s) m where
  rjoin = (>>= (state . runState))
  a `rbind` f = a >>= (state . runState . f)

instance {-# INCOHERENT #-} (MonadState s m) => BiModule (State s) (State s) m

-- | Proof that @f@ is always a left module over @'Codensity' f@:
--   - @   'ljoin' ('join' m)
--       = 'ljoin' ('Codensity' (\c -> 'runCodensity' m (\a -> 'runCodensity' a c)))
--       = (\c -> 'runCodensity' m (\a -> 'runCodensity' a c)) id
--       = 'runCodensity' m (\a -> 'runCodensity' a 'id')
--       = 'runCodensity' m 'ljoin' 'runCodensity' m (\x -> 'ljoin' x)
--       = (\k -> 'runCodensity' m (\x -> k ('ljoin' x))) 'id'
--       = 'ljoin' (Codensity (\k -> 'runCodensity' m (\x -> k ('ljoin' x))))
--       = 'ljoin' ('fmap' 'ljoin' m)@
--   - @'ljoin' ('pure' x) = 'ljoin' ('Codensity' (\x -> k x)) = (\k -> k x) 'id' = x@
instance (Functor f) => LeftModule (Codensity f) f where
  ljoin c = runCodensity c id
  a `lbind` f = runCodensity (f <$> a) id
