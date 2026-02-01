{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}

-- | This module should be used with @OverloadedRecordDot@ and/or @RebindableSyntax@ (and @RecordWildCards@).
module Control.Monad.Action.Records where

import Control.Monad qualified as M (join, (=<<))
import Control.Monad.TransformerStack
import Data.Constraint (Dict (..))
import Data.Kind (Constraint, Type)
import Prelude hiding ((<*>), (=<<), (>>), (>>=))
import Prelude qualified as P hiding ((=<<), (>>))

infixl 1 >>=

infixr 1 =<<

infixl 1 >>

infixr 1 >=>

infixr 1 <=<

infixl 4 <*>

-- | Every @'LeftAction'@ @l@ should satisfy the following laws:
--
-- * @l.'join' '.' 'Control.Monad.join' = l.'join' '.' 'fmap' l.'join'@
--
-- * @l.'join' '.' 'pure' = 'id'@
--
-- All of the operators should match the default implementations in "Control.Monad.Action" and "Control.Monad.Left".
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

-- | Every @'RightAction'@ @r@ should satisfy the following laws:
--
-- * @r.'join' '.' 'fmap' 'Control.Monad.join' = r.'join' '.' r.'join'@
--
-- * @r.'join' '.' 'fmap' 'pure' = 'id'@
--
-- All of the operators should match the default implementations in "Control.Monad.Action" and "Control.Monad.Right".
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

-- | Every @'BiAction'@ @b@ should satisfy the following laws:
--
-- * @b.'right'.'join' '.' b.'left'.'join' = b.'left'.'join' '.' 'fmap' b.'right'.'join'
data BiAction (action :: (Type -> Type) -> (Type -> Type) -> Constraint) where
  BiAction ::
    { left :: LeftAction action,
      right :: RightAction action
    } ->
    BiAction action

-- | @'MonadHomomorphism c'@ means that, whenever @c m n@, there is a monad homomorphism @'hom'@ from @m@ to @n@.
class MonadHomomorphism (c :: (Type -> Type) -> (Type -> Type) -> Constraint) where
  hom :: forall m n a. (c m n) => m a -> n a
  mDict :: forall m n. (c m n) => (Dict (Monad m), Dict (Monad n))

-- | Two-sided action induced by a monad homomorphism.
monadMorphAction :: forall action. (MonadHomomorphism action) => BiAction action
monadMorphAction =
  let left =
        let join :: forall m n a. (action m n) => m (n a) -> n a
            join = case mDict @action @m @n of (_, Dict) -> M.join . hom @action
            (>>=) :: forall m n a b. (action m n) => m a -> (a -> n b) -> n b
            (>>=) = case mDict @action @m @n of (_, Dict) -> (P.>>=) . hom @action
            (=<<) :: forall m n a b. (action m n) => (a -> n b) -> m a -> n b
            (=<<) = flip (>>=)
            (>=>) :: forall m n a b c. (action m n) => (a -> m b) -> (b -> n c) -> a -> n c
            f >=> g = \x -> f x >>= g
            (<=<) :: forall m n a b c. (action m n) => (b -> n c) -> (a -> m b) -> a -> n c
            (<=<) = flip (>=>)
            (>>) :: forall m n a b. (action m n) => m a -> n b -> n b
            a >> b = a >>= const b
            (<*>) :: forall m n a b. (action m n) => m (a -> b) -> n a -> n b
            (<*>) = case mDict @action @m @n of (_, Dict) -> (P.<*>) . hom @action
         in LeftAction {..} :: LeftAction action
      right =
        let join :: forall m n a. (action m n) => n (m a) -> n a
            join = case mDict @action @m @n of (_, Dict) -> (hom @action M.=<<)
            (>>=) :: forall m n a b. (action m n) => n a -> (a -> m b) -> n b
            (>>=) = flip (=<<)
            (=<<) :: forall m n a b. (action m n) => (a -> m b) -> n a -> n b
            (=<<) = case mDict @action @m @n of (_, Dict) -> (M.=<<) . (hom @action .)
            (>=>) :: forall m n a b c. (action m n) => (a -> n b) -> (b -> m c) -> a -> n c
            f >=> g = \x -> f x >>= g
            (<=<) :: forall m n a b c. (action m n) => (b -> m c) -> (a -> n b) -> a -> n c
            (<=<) = flip (>=>)
            (>>) :: forall m n a b. (action m n) => n a -> m b -> n b
            a >> b = a >>= const b
            (<*>) :: forall m n a b. (action m n) => n (a -> b) -> m a -> n b
            f <*> x = case mDict @action @m @n of (_, Dict) -> f P.<*> hom @action x
         in RightAction {..} :: RightAction action
   in BiAction {..}

instance MonadHomomorphism MonadTransStack where
  hom = liftStack
  mDict = (Dict, Dict)

transformerStackAction :: BiAction MonadTransStack
transformerStackAction = monadMorphAction @MonadTransStack
