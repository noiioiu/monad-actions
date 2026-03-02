{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Control.Monad.Action
-- Description : monad actions
-- Copyright   : © noiioiu
-- License     : LGPL-2
-- Maintainer  : noiioiu@cocaine.ninja
-- Stability   : experimental
-- Portability : not portable
--
-- Given a monad \(M\) on a category \(\mathcal{D}\) with unit \(\eta\) and
-- multiplication \(\mu\) and a functor \(F\) from \(\mathcal{C}\) to \(\mathcal{D}\),
-- a left (or outer) monad action of \(M\) on \(F\) is a natural transformation
-- \(\nu: M \circ F \to F\) such that the following two laws hold:
--
-- * \(\nu \cdot (\eta \circ F) = \mathrm{id}_F\)
-- * \(\nu \cdot (\mu \circ F) = \nu \cdot (M \circ \nu)\)
--
-- We also say that \(F\) is a left module over \(M\).  In the case
-- \(\mathcal{C} = \mathcal{D}\), a left monad module is a left monoid module
-- object in the category of endofunctors on \(\mathcal{C}\).  We may also
-- call \(\nu\) the scalar multiplication of the module by the monad, by analogy
-- with ring modules, which are monoid module objects in the category of abelian groups
-- with tensor product as the monoidal product (rings are just monoid objects in this
-- category).
--
-- Right (or inner) monad actions are defined similarly.
--
-- See [this blog post](https://stringdiagram.com/2023/04/23/monad-actions/) by Dan Marsden
-- or the paper /Modules over monads and their algebras/ by Piróg, Wu, and Gibbons.
module Control.Monad.Action
  ( LeftModule (..),
    RightModule (..),
    BiModule (..),
  )
where

import Control.Monad (join)
import Control.Monad.Accum (MonadAccum (..))
import Control.Monad.Action.TH (mkMTLActions, (#))
import Control.Monad.Codensity (Codensity (..))
import Control.Monad.Error.Class (MonadError (..), liftEither)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Identity (Identity (..))
import Control.Monad.RWS.Class (MonadRWS)
import Control.Monad.Reader.Class (MonadReader (..))
import Control.Monad.State ()
import Control.Monad.State.Class (MonadState (..))
import Control.Monad.State.Strict ()
import Control.Monad.Trans.Accum (Accum, runAccum)
import Control.Monad.Trans.Except (ExceptT (..), runExceptT)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.Reader ()
import Control.Monad.Trans.Writer ()
import Control.Monad.TransformerStack (IsRWS (..), IsReader (..), IsState (..), IsWriter (..), MonadTransStack (..), rws)
import Control.Monad.Writer.CPS ()
import Control.Monad.Writer.Class (MonadWriter (..))
import Control.Monad.Writer.Strict ()
import Data.Functor.Compose (Compose (..))
import Data.List.NonEmpty qualified as NE (NonEmpty, toList)
import Data.Maybe (catMaybes, mapMaybe)
import Language.Haskell.TH (Exp (..), Type (..))

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

instance {-# OVERLAPS #-} (Monad n, Monad m, MonadTransStack m n) => LeftModule m n where
  ljoin = join . liftStack
  lbind = (>>=) . liftStack

instance {-# OVERLAPS #-} (Monad n, Monad m, MonadTransStack m n) => RightModule m n where
  rjoin = (liftStack =<<)
  rbind = flip $ (=<<) . (liftStack .)

instance {-# OVERLAPS #-} (Monad n, Monad m, MonadTransStack m n) => BiModule m m n

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
  a `rbind` f = a >>= liftIO . f

instance {-# INCOHERENT #-} (MonadIO m) => BiModule IO IO m

-- | No laws are given in the documentation for @'MonadError'@, but we assume
--   @'liftEither'@ is a monad homomorphism.
instance {-# INCOHERENT #-} (MonadError e m) => LeftModule (Either e) m where
  ljoin = join . liftEither
  a `lbind` f = liftEither a >>= f

instance {-# INCOHERENT #-} (MonadError e m) => RightModule (Either e) m where
  rjoin = (>>= liftEither)
  a `rbind` f = a >>= liftEither . f

instance {-# INCOHERENT #-} (MonadError e m) => BiModule (Either e) (Either e) m

-- | For every @'MonadReader'@ instance defined in "Control.Monad.Reader.Class", @'reader'@ is a monad homomorphism.
$(mkMTLActions ''IsReader (VarE 'runReader) (VarE 'reader) (\case AppT _ r -> ConT ''MonadReader # r; _ -> TupleT 0))

-- | For every @'MonadWriter'@ instance defined in "Control.Monad.Writer.Class", @'writer' '.' 'runWriter'@ is a monad homomorphism.
$(mkMTLActions ''IsWriter (VarE 'runWriter) (VarE 'writer) (\case AppT _ w -> ConT ''MonadWriter # w; _ -> TupleT 0))

-- | For every @'MonadState'@ instance defined in "Control.Monad.State.Class", @'state' '.' 'runState'@ is a monad homomorphism.
$(mkMTLActions ''IsState (VarE 'runState) (VarE 'state) (\case AppT _ s -> ConT ''MonadState # s; _ -> TupleT 0))

$(mkMTLActions ''IsRWS (VarE 'runRWS) (VarE 'rws) (\case AppT (AppT (AppT _ r) w) s -> ConT ''MonadRWS # r # w # s; _ -> TupleT 0))

-- | For every lawful @'MonadAccum'@ instance, @'accum' '.' 'runAccum'@ is a monad homomorphism.
instance {-# INCOHERENT #-} (MonadAccum w m) => LeftModule (Accum w) m where
  ljoin = join . accum . runAccum
  a `lbind` f = accum (runAccum a) >>= f

instance {-# INCOHERENT #-} (MonadAccum w m) => RightModule (Accum w) m where
  rjoin = (>>= (accum . runAccum))
  a `rbind` f = a >>= accum . runAccum . f

instance {-# INCOHERENT #-} (MonadAccum w m) => BiModule (Accum w) (Accum w) m

-- | Proof that @f@ is always a left module over @t'Codensity' f@:
--
--   * @   'ljoin' ('join' m)
--       = 'ljoin' ('Codensity' (\\c -> 'runCodensity' m (\\a -> 'runCodensity' a c)))
--       = (\\c -> 'runCodensity' m (\\a -> 'runCodensity' a c)) id
--       = 'runCodensity' m (\\a -> 'runCodensity' a 'id')
--       = 'runCodensity' m 'ljoin' 'runCodensity' m (\\x -> 'ljoin' x)
--       = (\\k -> 'runCodensity' m (\\x -> k ('ljoin' x))) 'id'
--       = 'ljoin' ('Codensity' (\\k -> 'runCodensity' m (\\x -> k ('ljoin' x))))
--       = 'ljoin' ('fmap' 'ljoin' m)@
--
--   * @'ljoin' ('pure' x) = 'ljoin' ('Codensity' (\\x -> k x)) = (\\k -> k x) 'id' = x@
instance (Functor f) => LeftModule (Codensity f) f where
  ljoin c = runCodensity c id
  a `lbind` f = runCodensity (f <$> a) id
