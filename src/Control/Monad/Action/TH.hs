{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Monad.Action.TH where

import Control.Monad
import Control.Monad.Trans
import Language.Haskell.TH

mkMonadTransLeftActionInstances :: Q [Dec]
mkMonadTransLeftActionInstances =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        forM instances $ \case
          InstanceD _ ct (AppT (ConT _) ty) _ ->
            do
              m <- VarT <$> newName "m"
              let ct' = (ct ++ [AppT (ConT ''Monad) m])
              let ty' = AppT (AppT (ConT $ mkName "LeftModule") m) (AppT ty m)
              pure $ InstanceD (Just Overlaps) ct' ty' [ValD (VarP $ mkName "ljoin") (NormalB (VarE $ mkName "monadTransLScale")) []]
          _ -> fail "Not an instance"
      _ -> pure []

mkMonadTransRightActionInstances :: Q [Dec]
mkMonadTransRightActionInstances =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        forM instances $ \case
          InstanceD _ ct (AppT (ConT _) ty) _ ->
            do
              m <- VarT <$> newName "m"
              let ct' = (ct ++ [AppT (ConT ''Monad) m])
              let ty' = AppT (AppT (ConT $ mkName "RightModule") m) (AppT ty m)
              pure $ InstanceD (Just Overlaps) ct' ty' [ValD (VarP $ mkName "rjoin") (NormalB (VarE $ mkName "monadTransRScale")) []]
          _ -> fail "Not an instance"
      _ -> pure []

mkMonadTransBiActionInstances :: Q [Dec]
mkMonadTransBiActionInstances =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        forM instances $ \case
          InstanceD _ ct (AppT (ConT _) ty) _ ->
            do
              m <- VarT <$> newName "m"
              let ct' =
                    ( ct
                        ++ [ AppT (ConT ''Monad) m,
                             AppT (AppT (ConT $ mkName "LeftModule") m) (AppT ty m),
                             AppT (AppT (ConT $ mkName "RightModule") m) (AppT ty m)
                           ]
                    )
              let ty' = AppT (AppT (AppT (ConT $ mkName "BiModule") m) m) (AppT ty m)
              pure $ InstanceD (Just Overlaps) ct' ty' [ValD (VarP $ mkName "bijoin") (NormalB (VarE $ mkName "monadTransBiScale")) []]
          _ -> fail "Not an instance"
      _ -> pure []
