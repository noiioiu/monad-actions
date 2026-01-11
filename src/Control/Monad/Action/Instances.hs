{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Control.Monad.Action.Instances where

import Control.Monad (join)
import Control.Monad.Action.Class
import Control.Monad.Action.TH
import Control.Monad.Except (runExceptT)
import Control.Monad.Identity (Identity (..))
import Control.Monad.Morph ()
import Control.Monad.Trans ()
import Control.Monad.Trans.Compose ()
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.Reader ()
import Control.Monad.Trans.Select ()
import Control.Monad.Trans.State.Lazy qualified as L ()
import Control.Monad.Trans.State.Strict qualified as S ()
import Control.Monad.Trans.Writer.CPS qualified as C ()
import Control.Monad.Trans.Writer.Lazy qualified as L ()
import Control.Monad.Trans.Writer.Strict qualified as S ()
import Data.Functor.Compose (Compose (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (catMaybes)

$(mkMonadTransLeftActionInstances)
$(mkMonadTransRightActionInstances)
$(mkMonadTransBiActionInstances)

instance (Monad m) => LeftModule m m where ljoin = join

instance (Monad m) => RightModule m m where rjoin = join

instance (Monad m) => BiModule m m m

instance (Functor f) => LeftModule Identity f where ljoin = runIdentity

instance (Functor f) => RightModule Identity f where rjoin = fmap runIdentity

instance (Functor f) => BiModule Identity Identity f

instance RightModule Maybe [] where rjoin = catMaybes

instance LeftModule Maybe [] where ljoin = concat

instance LeftModule NE.NonEmpty [] where ljoin = concat

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

instance (Monad m, Functor f, LeftModule m n) => LeftModule m (Compose n f) where
  ljoin = Compose . ljoin . fmap getCompose

instance (Monad m, Functor f, RightModule m n) => RightModule m (Compose f n) where
  rjoin = Compose . fmap rjoin . getCompose

instance (Monad s, Monad t, Functor f, LeftModule s u, RightModule t v) => BiModule s t (Compose u (Compose f v))

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
