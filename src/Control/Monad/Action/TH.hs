{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Control.Monad.Action.TH (mkMonadTransModuleInstances) where

import Control.Monad
import Control.Monad.Trans
import Language.Haskell.TH

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

-- type family IsStackOver (m :: Type -> Type) (n :: Type -> Type) :: Bool where
--   IsStackOver m m = True
--   IsStackOver m (ExceptT e n) = IsStackOver m n
--   IsStackOver m (MaybeT n) = IsStackOver m n
--   ...
--   IsStackOver _ _ = False

-- class (IsStackOver m n ~ True) => LiftStack m n where
--   liftStack :: forall a. m a -> n a

-- instance LiftStack m m where
--   liftStack = id

-- instance (Monad m, Monad n, LiftStack m n, IsStackOver m (ExceptT e n) ~ True) => LiftStack m (ExceptT e n) where
--   liftStack = lift . liftStack

-- instance (Monad m, Monad n, LiftStack m n, IsStackOver m (MaybeT n) ~ True) => LiftStack m (MaybeT n) where
--   liftStack = lift . liftStack

mkIsStackover :: Q [Dec]
mkIsStackover =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        do
          m <- newName "m"
          n <- newName "n"
          let fName = mkName "IsStackOver"
          let mSig = AppT (AppT ArrowT $ ConT ''Type) $ ConT ''Type
              --   IsStackOver m m = True
              eqCase = TySynEqn Nothing (AppT (AppT (ConT fName) (VarT m)) (VarT m)) (ConT 'True)
              mtCases =
                instances
                  >>= \case
                    InstanceD _ _ (AppT (ConT _) t) _ ->
                      pure $
                        --   IsStackOver m (t n) = IsStackOver m n
                        TySynEqn
                          Nothing
                          (AppT (AppT (ConT fName) (VarT m)) (AppT t $ VarT n))
                          (AppT (AppT (ConT fName) (VarT m)) (VarT n))
                    _ -> []

              --   IsStackOver _ _ = True
              defCase = TySynEqn Nothing (AppT (AppT (ConT fName) WildCardT) WildCardT) (ConT 'False)
          pure $
            [ ClosedTypeFamilyD
                ( TypeFamilyHead
                    fName
                    [KindedTV m BndrReq mSig, KindedTV n BndrReq mSig]
                    (KindSig $ ConT ''Bool)
                    Nothing
                )
                $ eqCase : mtCases ++ [defCase]
            ]
      _ -> pure []

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
              let ctB =
                    ct
                      ++ [ AppT (ConT ''Monad) m,
                           AppT (AppT (ConT $ mkName "LeftModule") m) (AppT ty m),
                           AppT (AppT (ConT $ mkName "RightModule") m) (AppT ty m)
                         ]
              let tyL = AppT (AppT (ConT $ mkName "LeftModule") m) (AppT ty m)
              let tyR = AppT (AppT (ConT $ mkName "RightModule") m) (AppT ty m)
              let tyB = AppT (AppT (AppT (ConT $ mkName "BiModule") m) m) (AppT ty m)
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
