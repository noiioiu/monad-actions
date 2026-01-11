{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Monad.Action.TH where

import Control.Monad
import Control.Monad.Action.Class
import Control.Monad.Trans
import Language.Haskell.TH

mkMonadTransLeftActionInstances :: Q [Dec]
mkMonadTransLeftActionInstances =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        forM instances $ \case
          InstanceD ol ct (AppT (ConT _) ty) _ ->
            do
              m <- VarT <$> newName "m"
              let ct' = (ct ++ [AppT (ConT ''Monad) m])
              let ty' = AppT (AppT (ConT ''LeftModule) m) (AppT ty m)
              pure $ InstanceD ol ct' ty' [ValD (VarP 'ljoin) (NormalB (VarE 'monadTransLScale)) []]
          _ -> undefined
      _ -> pure []

mkMonadTransRightActionInstances :: Q [Dec]
mkMonadTransRightActionInstances =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        forM instances $ \case
          InstanceD ol ct (AppT (ConT _) ty) _ ->
            do
              m <- VarT <$> newName "m"
              let ct' = (ct ++ [AppT (ConT ''Monad) m])
              let ty' = AppT (AppT (ConT ''RightModule) m) (AppT ty m)
              pure $ InstanceD ol ct' ty' [ValD (VarP 'rjoin) (NormalB (VarE 'monadTransRScale)) []]
          _ -> undefined
      _ -> pure []

mkMonadTransBiActionInstances :: Q [Dec]
mkMonadTransBiActionInstances =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        forM instances $ \case
          InstanceD ol ct (AppT (ConT _) ty) _ ->
            do
              m <- VarT <$> newName "m"
              let ct' = (ct ++ [AppT (ConT ''Monad) m, AppT (AppT (ConT ''LeftModule) m) (AppT ty m), AppT (AppT (ConT ''RightModule) m) (AppT ty m)])
              let ty' = AppT (AppT (AppT (ConT ''BiModule) m) m) (AppT ty m)
              pure $ InstanceD ol ct' ty' [ValD (VarP 'bijoin) (NormalB (VarE 'monadTransBiScale)) []]
          _ -> undefined
      _ -> pure []
