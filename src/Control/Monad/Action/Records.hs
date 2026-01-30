{-# LANGUAGE DuplicateRecordFields #-}

-- | This module should be used with @OverloadedRecordDot@ and/or @RebindableSyntax@ (and @RecordWildCards@).
module Control.Monad.Action.Records where

import Data.Kind (Constraint, Type)

infixl 1 >>=

infixr 1 =<<

infixl 1 >>

infixr 1 >=>

infixr 1 <=<

infixl 4 <*>

data LeftAction (action :: (Type -> Type) -> (Type -> Type) -> Constraint) where
  LeftAction ::
    { -- | left monad action scalar multiplication
      join :: forall m f a. (action m f) => m (f a) -> f a,
      -- | left monad action bind
      (>>=) :: forall m f a b. (action m f) => m a -> (a -> f b) -> f b,
      -- | left monad action bind with arguments reversed
      (=<<) :: forall m f a b. (action m f) => (a -> f b) -> m a -> f b,
      -- | left to right Kleisli arrow scalar multiplication induced by a left monad action
      (>=>) :: forall m f a b c. (action m f) => (a -> m b) -> (b -> f c) -> a -> f c,
      -- | right to left Kleisli arrow scalar multiplication induced by a left monad action
      (<=<) :: forall m f a b c. (action m f) => (b -> f c) -> (a -> m b) -> a -> f c,
      -- | left monad action sequencing operator
      (>>) :: forall m f a b. (action m f) => m a -> f b -> f b,
      -- | scalar sequential application, used for desugaring applicative do blocks
      (<*>) :: forall m f a b. (action m f) => m (a -> b) -> f a -> f b
    } ->
    LeftAction action

data RightAction (action :: (Type -> Type) -> (Type -> Type) -> Constraint) where
  RightAction ::
    { -- | right monad action scalar multiplication
      join :: forall m f a. (action m f) => f (m a) -> f a,
      -- | right monad action bind
      (>>=) :: forall m f a b. (action m f) => f a -> (a -> m b) -> f b,
      -- | right monad action bind with arguments reversed
      (=<<) :: forall m f a b. (action m f) => (a -> m b) -> f a -> f b,
      -- | left to right Kleisli arrow scalar multiplication induced by a right monad action
      (>=>) :: forall m f a b c. (action m f) => (a -> f b) -> (b -> m c) -> a -> f c,
      -- | right to left Kleisli arrow scalar multiplication induced by a right monad action
      (<=<) :: forall m f a b c. (action m f) => (b -> m c) -> (a -> f b) -> a -> f c,
      -- | right monad action sequencing operator
      (>>) :: forall m f a b. (action m f) => f a -> m b -> f b,
      -- | scalar sequential application, used for desugaring applicative do blocks
      (<*>) :: forall m f a b. (action m f) => f (a -> b) -> m a -> f b
    } ->
    RightAction action
