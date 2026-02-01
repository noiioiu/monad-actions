{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}

-- | This module should be used with @OverloadedRecordDot@ and/or @RebindableSyntax@ (and @RecordWildCards@).
module Control.Monad.Action.Records where

import Control.Monad qualified as M (join, (=<<))
import Control.Monad.TransformerStack
import Data.Kind (Constraint, Type)
import Prelude hiding ((<*>), (=<<), (>>), (>>=))
import Prelude qualified as P hiding ((=<<), (>>))

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

data BiAction (action :: (Type -> Type) -> (Type -> Type) -> Constraint) where
  BiAction ::
    { left :: LeftAction action,
      right :: RightAction action
    } ->
    BiAction action

transformerStackAction :: BiAction LiftStack
transformerStackAction =
  let left =
        let join :: forall m n a. (LiftStack m n) => m (n a) -> n a
            join = M.join . liftStack
            (>>=) :: forall m n a b. (LiftStack m n) => m a -> (a -> n b) -> n b
            (>>=) = (P.>>=) . liftStack
            (=<<) :: forall m n a b. (LiftStack m n) => (a -> n b) -> m a -> n b
            (=<<) = flip (>>=)
            (>=>) :: forall m n a b c. (LiftStack m n) => (a -> m b) -> (b -> n c) -> a -> n c
            f >=> g = \x -> f x >>= g
            (<=<) :: forall m n a b c. (LiftStack m n) => (b -> n c) -> (a -> m b) -> a -> n c
            (<=<) = flip (>=>)
            (>>) :: forall m n a b. (LiftStack m n) => m a -> n b -> n b
            a >> b = a >>= const b
            (<*>) :: forall m n a b. (LiftStack m n) => m (a -> b) -> n a -> n b
            (<*>) = (P.<*>) . liftStack
         in LeftAction {..} :: LeftAction LiftStack
      right =
        let join :: forall m n a. (LiftStack m n) => n (m a) -> n a
            join = (liftStack M.=<<)
            (>>=) :: forall m n a b. (LiftStack m n) => n a -> (a -> m b) -> n b
            (>>=) = flip (=<<)
            (=<<) :: forall m n a b. (LiftStack m n) => (a -> m b) -> n a -> n b
            (=<<) = (M.=<<) . (liftStack .)
            (>=>) :: forall m n a b c. (LiftStack m n) => (a -> n b) -> (b -> m c) -> a -> n c
            f >=> g = \x -> f x >>= g
            (<=<) :: forall m n a b c. (LiftStack m n) => (b -> m c) -> (a -> n b) -> a -> n c
            (<=<) = flip (>=>)
            (>>) :: forall m n a b. (LiftStack m n) => n a -> m b -> n b
            a >> b = a >>= const b
            (<*>) :: forall m f a b. (LiftStack m f) => f (a -> b) -> m a -> f b
            f <*> x = f P.<*> liftStack x
         in RightAction {..} :: RightAction LiftStack
   in BiAction {..}
