{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Control.Monad.Action
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Data.Functor.Compose
import Test.QuickCheck
import Test.QuickCheck.Checkers
import Control.Monad.Action.Left qualified as L
import Control.Monad.Action.Right qualified as R
import Control.Applicative
import Control.Monad.Except

leftmodule ::
  forall m f a.
  ( LeftModule m f,
    Arbitrary (f a),
    Arbitrary (m (m (f a))),
    Show (f a),
    Show (m (m (f a))),
    EqProp (f a)
  ) =>
  TestBatch
leftmodule =
  ( "left module laws",
    [ ("left identity", property leftP),
      ("associativity", property assocP)
    ]
  )
  where
    leftP :: f a -> Property
    assocP :: m (m (f a)) -> Property

    leftP a = ljoin (pure @m a) =-= a
    assocP a = ljoin (join a) =-= ljoin (fmap ljoin a)

rightmodule ::
  forall m f a.
  ( RightModule m f,
    Arbitrary (f a),
    Arbitrary (f (m (m a))),
    Show (f a),
    Show (f (m (m a))),
    EqProp (f a)
  ) =>
  TestBatch
rightmodule =
  ( "right module laws",
    [ ("right identity", property rightP),
      ("associativity", property assocP)
    ]
  )
  where
    rightP :: f a -> Property
    assocP :: f (m (m a)) -> Property

    rightP a = rjoin (fmap (pure @m) a) =-= a
    assocP a = rjoin (fmap join a) =-= rjoin (rjoin a)

bimodule ::
  forall s t f a.
  ( BiModule s t f,
    Arbitrary (f a),
    Arbitrary (s (f (t a))),
    Show (f a),
    Show (s (f (t a))),
    EqProp (f a)
  ) =>
  TestBatch
bimodule =
  ( "bimodule laws",
    [ ("associativity 1", property assoc1P),
      ("associativity 2", property assoc2P)
    ]
  )
  where
    assoc1P :: s (f (t a)) -> Property
    assoc2P :: s (f (t a)) -> Property

    assoc1P a = bijoin a =-= rjoin (ljoin a)
    assoc2P a = bijoin a =-= ljoin (fmap rjoin a)

instance (CoArbitrary s, Arbitrary (m (a, s)), Function s) => Arbitrary (StateT s m a) where
  arbitrary = StateT . applyFun <$> arbitrary

instance (Show s, Arbitrary s, EqProp (m (a, s))) => EqProp (StateT s m a) where
  a =-= b = runStateT a =-= runStateT b

instance (Arbitrary (m (Maybe a))) => Arbitrary (MaybeT m a) where
  arbitrary = MaybeT <$> arbitrary

instance (EqProp (m (Maybe a))) => EqProp (MaybeT m a) where
  MaybeT x =-= MaybeT y = x =-= y

instance (Arbitrary (m (Either e a))) => Arbitrary (ExceptT e m a) where
  arbitrary = ExceptT <$> arbitrary

instance (EqProp (m (Either e a))) => EqProp (ExceptT e m a) where
  ExceptT x =-= ExceptT y = x =-= y



rightmodulestate ::
  forall m s a.
  ( Monad m,
    Arbitrary a,
    Function s,
    CoArbitrary s,
    Arbitrary (m (a, s)),
    Show s,
    Show (m (a, s)),
    Arbitrary (m (m a, s)),
    Show (m (m a, s)),
    Arbitrary s,
    EqProp (m (a, s)),
    Arbitrary (m (m (m a), s)),
    Show (m (m (m a), s))
  ) =>
  TestBatch
rightmodulestate =
  ( "right module laws",
    [ ("right identity", property rightP),
      ("associativity", property assocP)
    ]
  )
  where
    rightP :: Fun s (m (a, s)) -> Property
    assocP :: Fun s (m (m (m a), s)) -> Property

    rightP a = rjoin (fmap (pure @m) (StateT $ applyFun a)) =-= StateT (applyFun a)
    assocP a = rjoin (fmap join (StateT $ applyFun a)) =-= rjoin (rjoin (StateT $ applyFun a))

leftmodulestate ::
  forall m s a.
  ( Monad m,
    Arbitrary a,
    Function s,
    CoArbitrary s,
    Arbitrary (m (Fun s (m (a, s)))),
    Show (m (Fun s (m (a, s)))),
    Arbitrary (m (m (Fun s (m (a, s))))),
    Show (m (m (Fun s (m (a, s))))),
    EqProp (m (StateT s m a)),
    Show s,
    Arbitrary s,
    EqProp (m (a, s))
  ) =>
  TestBatch
leftmodulestate =
  ( "left module laws",
    [ ("left identity", property leftP),
      ("associativity", property assocP)
    ]
  )
  where
    leftP :: m (Fun s (m (a, s))) -> Property
    assocP :: m (m (Fun s (m (a, s)))) -> Property

    leftP a = ljoin (pure @m (StateT . applyFun <$> a)) =-= (StateT . applyFun <$> a)
    assocP a = ljoin (join (fmap (StateT . applyFun) <$> a)) =-= ljoin (fmap ljoin (fmap (StateT . applyFun) <$> a))

bimodulestate ::
  forall m s a.
  ( Monad m,
    Arbitrary a,
    Arbitrary (m (Fun s (m (m a), s))),
    Show (m (Fun s (m (m a), s))),
    Arbitrary (m (Fun s (m (m a, s)))),
    Show (m (Fun s (m (m a, s)))),
    Show s,
    Arbitrary s,
    EqProp (m (a, s))
  ) =>
  TestBatch
bimodulestate =
  ( "bimodule laws",
    [ ("associativity 1", property assoc1P),
      ("associativity 2", property assoc2P)
    ]
  )
  where
    assoc1P :: m (Fun s (m (m a, s))) -> Property
    assoc2P :: m (Fun s (m (m a, s))) -> Property

    assoc1P a = bijoin (StateT . applyFun <$> a) =-= rjoin (ljoin (StateT . applyFun <$> a))
    assoc2P a = bijoin (StateT . applyFun <$> a) =-= ljoin (fmap rjoin (StateT . applyFun <$> a))

instance (Show s, Arbitrary s, EqProp (m a)) => EqProp (ReaderT s m a) where
  a =-= b = runReaderT a =-= runReaderT b

rightmodulereader ::
  forall m s a.
  ( Monad m,
    Arbitrary a,
    Function s,
    CoArbitrary s,
    Arbitrary (m a),
    Arbitrary (m (m (m a))),
    Show (m a),
    Show (m (m (m a))),
    Show s,
    Arbitrary s,
    EqProp (m a)
  ) =>
  TestBatch
rightmodulereader =
  ( "right module laws",
    [ ("right identity", property rightP),
      ("associativity", property assocP)
    ]
  )
  where
    rightP :: Fun s (m a) -> Property
    assocP :: Fun s (m (m (m a))) -> Property

    rightP a = rjoin (fmap (pure @m) (ReaderT $ applyFun a)) =-= ReaderT (applyFun a)
    assocP a = rjoin (fmap join (ReaderT $ applyFun a)) =-= rjoin (rjoin (ReaderT $ applyFun a))

instance (Arbitrary (m (a, w))) => Arbitrary (WriterT w m a) where
  arbitrary = WriterT <$> arbitrary

instance (EqProp (m (a, w))) => EqProp (WriterT w m a) where
  a =-= b = runWriterT a =-= runWriterT b

ldotest :: StateT Char [] Int
ldotest = L.do x <- [1,2,3,4,5]
               g <- get @_ @(StateT Char [])
               put @_ @(StateT Char []) $ succ g
               pure $ x*x

rdotest :: Compose ZipList [] Int
rdotest = R.do x <- Compose $ ZipList [[1,2,3], [4,5,6], [7,8,9]]
               [x*x, x]

main :: IO ()
main =
  print (getCompose rdotest) >>
  print (runStateT ldotest 'a') >>
  mapM_
    quickBatch
    [ leftmodule @Maybe @[] @Int
    , rightmodule @Maybe @[] @Int
    , rightmodule @(Either Int) @Maybe @Int
    , leftmodule @(Either Char) @Maybe @Int
    , bimodule @(Either Char) @(Either Bool) @Maybe @Int
    , bimodule @(Either Char) @(Either Int) @Maybe @Int
    , bimodule @Maybe @(Either Int) @Maybe @Int
    , bimodule @(Either Char) @Maybe @Maybe @Int

    , rightmodule @(Either Int) @(MaybeT []) @Int
    , leftmodule @(Either Int) @(MaybeT []) @Int
    , bimodule @(Either Int) @(Either [Bool]) @(MaybeT []) @Int

    , rightmodule @(Either (Sum Int)) @(ExceptT (Sum Int) []) @Int
    , leftmodule @(Either (Sum Int)) @(ExceptT (Sum Int) []) @Int
    , bimodule @(Either (Sum Int)) @(Either (Sum Int)) @(ExceptT (Sum Int) []) @Int

    , rightmodule @Maybe @(ExceptT (Sum Int) []) @Int
    , leftmodule @Maybe @(ExceptT (Sum Int) []) @Int
    , bimodule @(Either (Sum Int)) @Maybe @(ExceptT (Sum Int) []) @Int

    , rightmodule @Maybe @(MaybeT []) @Int
    , leftmodule @Maybe @(MaybeT []) @Int
    , bimodule @Maybe @Maybe @(MaybeT []) @Int

      --, bimodule @Maybe @Maybe @[] @Int
      --, leftmodule @[] @(Compose [] ((,) Bool)) @Bool
      --, rightmodule @Maybe @(Compose ((,) Bool) []) @Bool
      --, bimodule @Maybe @Maybe @(Compose [] (Compose (Either Bool) Maybe)) @Bool
      --, leftmodule @Maybe @[] @Int
      --, rightmodule @Maybe @[] @Int
      --, bimodule @Maybe @Maybe @[] @Int
      --, bimodule @Maybe @[] @[] @Int
      --, bimodule @[] @Maybe @[] @Int
      --, bimodule @[] @[] @[] @Int
      --, leftmodule @Identity @Identity @Int

      , rightmodulestate @(WriterT (Product Int) (Either Double)) @Int @Char
      --, rightmodulereader @(WriterT (Product Int) (Either Double)) @Int @Char
      --, rightmodulereader @(Either Bool) @Char @Int

      -- , leftmodulestate @(Writer (Sum Int)) @Int @Bool
      -- , rightmodulestate @(Writer (Sum Int)) @Int @Bool
      -- , rightmodulestate @(Either Bool) @Int @Bool
      -- , bimodulestate @(WriterT (Sum Int) Maybe) @Int @Bool
      -- , rightmodule @(Writer (Sum Float)) @(Writer (Sum Float)) @Int -- this should fail because Sum Float is not a monoid
      -- , leftmodule @(Writer (Sum Float)) @(Writer (Sum Float)) @Int -- this should fail because Sum Float is not a monoid
    ]
