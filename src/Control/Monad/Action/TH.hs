{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Monad.Action.TH (mkMonadTransModuleInstances) where

import Control.Monad
import Control.Monad.Trans
import Language.Haskell.TH

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

mkMonadTransModuleInstances :: Q [Dec]
mkMonadTransModuleInstances =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        fmap join . forM instances $ \case
          InstanceD _ ct (AppT (ConT _) ty) _ ->
            do
              m <- VarT <$> newName "m"
              let ct' = ct ++ [AppT (ConT ''Monad) m]
              let tyL = AppT (AppT (ConT $ mkName "LeftModule") m) (AppT ty m)
              let tyR = AppT (AppT (ConT $ mkName "RightModule") m) (AppT ty m)
              let tyB = AppT (AppT (AppT (ConT $ mkName "BiModule") m) m) (AppT ty m)
              let ctB =
                    ct
                      ++ [ AppT (ConT ''Monad) m,
                           AppT (AppT (ConT $ mkName "LeftModule") m) (AppT ty m),
                           AppT (AppT (ConT $ mkName "RightModule") m) (AppT ty m)
                         ]
              pure $
                fmap
                  (uncurry3 $ InstanceD (Just Overlaps))
                  [ ( ct',
                      tyL,
                      [ ValD
                          (VarP $ mkName "ljoin")
                          (NormalB (VarE $ mkName "monadTransLScale"))
                          []
                      ]
                    ),
                    ( ct',
                      tyR,
                      [ ValD
                          (VarP $ mkName "rjoin")
                          (NormalB (VarE $ mkName "monadTransRScale"))
                          []
                      ]
                    ),
                    ( ctB,
                      tyB,
                      [ ValD
                          (VarP $ mkName "bijoin")
                          (NormalB (VarE $ mkName "monadTransBiScale"))
                          []
                      ]
                    )
                  ]
          _ -> fail "Not an instance"
      _ -> pure []
