{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}

-- | This module should be used with @OverloadedRecordDot@ and/or @RebindableSyntax@ (and @RecordWildCards@).
module Control.Monad.Action.Records where

import Control.Monad qualified as M (Monad (..), join, (=<<))
import Control.Monad.Error.Class (MonadError, liftEither)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.RWS (MonadRWS, RWS, RWST (..), runRWS)
import Control.Monad.Reader (MonadReader (..), Reader, ReaderT (..), runReader)
import Control.Monad.State (MonadState (..), State, StateT (..), runState)
import Control.Monad.Trans.Writer (WriterT (..))
import Control.Monad.TransformerStack
import Control.Monad.Writer (MonadWriter (..), Writer, runWriter)
import Data.Bifunctor (second)
import Data.Constraint (Dict (..))
import Data.Kind (Constraint, Type)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (maybeToList)
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
transformerStackAction = monadMorphAction

-- | @m ':<:' n@ means that @m@ is a submonad of @n@. @'inject'@ must be a monic monad homomorphism.
class (Monad m, Monad n) => m :<: n where
  inject :: forall a. m a -> n a

instance MonadHomomorphism (:<:) where
  hom = inject
  mDict = (Dict, Dict)

submonadAction :: BiAction (:<:)
submonadAction = monadMorphAction

instance (Monad m) => m :<: m where
  inject = id

-- | A @'Maybe'@ is just a list of length at most 1.
instance Maybe :<: [] where
  inject = maybeToList

-- | A @'Data.List.NonEmpty.NonEmpty'@ is just a list of length at least 1.
instance NE.NonEmpty :<: [] where
  inject = NE.toList

-- | @'ReaderT'@ is just read-only @'StateT'@.
instance (m :<: n) => ReaderT s m :<: StateT s n where
  inject ReaderT {runReaderT} = StateT $ \s -> inject . fmap (,s) $ runReaderT s

-- | @'WriterT'@ is just append-only @'StateT'@.
instance (Monoid s, m :<: n) => WriterT s m :<: StateT s n where
  inject WriterT {runWriterT} = StateT $ \s -> inject @m @n . fmap (second (s <>)) $ runWriterT

-- | @'StateT'@ is just @'RWST'@ that ignores the read-only environment and doesn't append to the output.
instance (Monoid w, m :<: n) => StateT s m :<: RWST r w s n where
  inject StateT {runStateT} = RWST $ \_ s -> inject . fmap (\(a, t) -> (a, t, mempty)) $ runStateT s

-- | @'ReaderT'@ is just @'RWST'@ that ignores the state and doesn't append to the output.
--
--   Note: @'inject' \@('ReaderT' s m) \@('StateT' s n) '.' 'inject' \@('StateT' s n) \@('RWST' s w s k) =/= 'inject' \@('ReaderT' s m) \@('RWST' s w s k)@
instance (Monoid w, m :<: n) => ReaderT r m :<: RWST r w s n where
  inject ReaderT {runReaderT} = RWST $ \r s -> inject . fmap (,s,mempty) $ runReaderT r

-- | @'WriterT'@ is just @'RWST'@ that ignores the environment and state.
--
--   Note: @'inject' \@('WriterT' w m) \@('StateT' w n) '.' 'inject' \@('StateT' w n) \@('RWST' r w w k) =/= 'inject' \@('WriterT' w m) \@('RWST' r w w k)@
instance (Monoid w, m :<: n) => WriterT w m :<: RWST r w s n where
  inject WriterT {runWriterT} = RWST $ \_ s -> inject @m @n . fmap (\(a, w) -> (a, s, w)) $ runWriterT

-- | @'Embed' m n@ means that @m@ is the canonical monad for a class of which @n@ has an instance. @'embed'@ must be a monad homomorphism.
class (Monad m, Monad n) => Embed m n where
  embed :: forall a. m a -> n a

instance MonadHomomorphism Embed where
  hom = embed
  mDict = (Dict, Dict)

embeddingAction :: BiAction Embed
embeddingAction = monadMorphAction

instance (MonadIO m) => Embed IO m where
  embed = liftIO

instance (MonadState s m) => Embed (State s) m where
  embed = state . runState

instance (MonadReader r m) => Embed (Reader r) m where
  embed = reader . runReader

instance (MonadWriter w m) => Embed (Writer w) m where
  embed = writer . runWriter

instance (MonadRWS r w s m) => Embed (RWS r w s) m where
  embed t =
    ask P.>>= \r ->
      get P.>>= \s ->
        let (a, s', w) = runRWS t r s
         in put s'
              M.>> tell w
              M.>> pure a

instance (MonadError e m) => Embed (Either e) m where
  embed = liftEither
