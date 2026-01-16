{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Given a monad \(M\) on a category \(\mathcal{D}\) with unit \(\eta\) and
--     multiplication \(\mu\) and a functor \(F\) from \(\mathcal{C}\) to \(\mathcal{D}\),
--     a left monad action of \(M\) on \(F\) is a natural transformation \(\nu\) such that
--     the following two laws hold:
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
    monadTransLScale,
    monadTransRScale,
    monadTransBiScale,
  )
where

import Control.Monad (join)
import Control.Monad.Action.TH
import Control.Monad.Co ()
import Control.Monad.Codensity (Codensity (..))
import Control.Monad.Except (runExceptT)
import Control.Monad.Identity (Identity (..))
import Control.Monad.Morph
import Control.Monad.Morph ()
import Control.Monad.Trans ()
import Control.Monad.Trans.Compose ()
import Control.Monad.Trans.Except (ExceptT (..))
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

$(mkMonadTransLeftActionInstances)
$(mkMonadTransRightActionInstances)
$(mkMonadTransBiActionInstances)

instance {-# OVERLAPPING #-} (Monad m) => LeftModule m m where ljoin = join; lbind = (>>=)

instance {-# OVERLAPPING #-} (Monad m) => RightModule m m where rjoin = join; rbind = (>>=)

instance {-# OVERLAPPING #-} (Monad m) => BiModule m m m

instance {-# OVERLAPS #-} (Functor f) => LeftModule Identity f where ljoin = runIdentity

instance {-# OVERLAPS #-} (Functor f) => RightModule Identity f where rjoin = fmap runIdentity

instance {-# OVERLAPS #-} (Functor f) => BiModule Identity Identity f

instance RightModule Maybe [] where rjoin = catMaybes; rbind = flip mapMaybe

instance LeftModule Maybe [] where ljoin = concat; lbind = flip concatMap

instance LeftModule NE.NonEmpty [] where ljoin = concat; lbind = flip concatMap

instance RightModule NE.NonEmpty [] where rjoin = (>>= NE.toList)

instance BiModule Maybe Maybe []

instance BiModule Maybe [] []

instance BiModule [] Maybe []

instance BiModule NE.NonEmpty NE.NonEmpty []

instance BiModule [] NE.NonEmpty []

instance BiModule NE.NonEmpty [] []

instance BiModule Maybe NE.NonEmpty []

instance BiModule NE.NonEmpty Maybe []

instance RightModule (Either e) Maybe where
  rjoin (Just (Right x)) = Just x
  rjoin _ = Nothing

instance LeftModule (Either e) Maybe where
  ljoin (Right (Just x)) = Just x
  ljoin _ = Nothing

instance BiModule (Either e) (Either f) Maybe

instance BiModule (Either e) Maybe Maybe

instance BiModule Maybe (Either f) Maybe

instance {-# OVERLAPS #-} (Monad m, Functor f, LeftModule m n) => LeftModule m (Compose n f) where
  ljoin = Compose . ljoin . fmap getCompose
  a `lbind` f = Compose $ a `lbind` (getCompose . f)

instance {-# OVERLAPS #-} (Monad m, Functor f, RightModule m n) => RightModule m (Compose f n) where
  rjoin = Compose . fmap rjoin . getCompose
  a `rbind` f = Compose . fmap (`rbind` f) $ getCompose a

instance {-# OVERLAPS #-} (Monad s, Monad t, Functor f, LeftModule s u, RightModule t v) => BiModule s t (Compose u (Compose f v))

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
