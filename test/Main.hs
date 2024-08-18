{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Control.Monad.Action
import Data.Functor.Compose
import Test.QuickCheck
import Test.QuickCheck.Checkers

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

    assocP a = lact (join a) =-= lact (fmap lact a)
    leftP a = lact (return @m a) =-= a

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

    assocP a = ract (fmap join a) =-= ract (ract a)
    rightP a = ract (fmap (return @m) a) =-= a

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

    assoc1P a = biact a =-= ract (lact a)
    assoc2P a = biact a =-= lact (fmap ract a)

main :: IO ()
main =
  mapM_
    quickBatch
    [ leftmodule @Maybe @[] @Int,
      rightmodule @Maybe @[] @Int,
      bimodule @Maybe @Maybe @[] @Int,
      leftmodule @[] @(Compose [] ((,) Bool)) @Bool,
      rightmodule @[] @(Compose ((,) Bool) []) @Bool,
      bimodule @[] @Maybe @(Compose [] (Compose (Either Bool) Maybe)) @Bool
    ]
