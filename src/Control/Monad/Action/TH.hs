{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Control.Monad.Action.TH (mkMonadTransModuleInstances, mkIsStackOver, mkLiftStackInstances) where

import Control.Monad
import Control.Monad.Trans
import Language.Haskell.TH

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

infixl 5 #

(#) :: Type -> Type -> Type
(#) = AppT

mkLiftStackInstances :: Q [Dec]
mkLiftStackInstances =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        do
          m <- newName "m"
          n <- newName "n"
          let cName = mkName "LiftStack"
          -- instance LiftStack m m where
          --   liftStack = id
          let baseInstance =
                InstanceD
                  Nothing
                  []
                  (ConT cName # VarT m # VarT m)
                  [ValD (VarP $ mkName "liftStack") (NormalB $ VarE 'id) []]
              inductiveInstances =
                instances >>= \case
                  InstanceD _ ct (AppT (ConT _) t) _ ->
                    -- instance (Monad m, Monad n, LiftStack m n, IsStackOver m (t n) ~ True) => LiftStack m (t n) where
                    --   liftStack = lift . liftStack
                    pure $
                      InstanceD
                        Nothing
                        ( [ ConT ''Monad # VarT m,
                            ConT ''Monad # VarT n,
                            ConT cName # VarT m # VarT n,
                            EqualityT # (ConT (mkName "IsStackOver") # VarT m # (t # VarT n)) # PromotedT 'True
                          ]
                            ++ ct
                        )
                        (ConT cName # VarT m # (t # VarT n))
                        [ ValD
                            (VarP $ mkName "liftStack")
                            (NormalB $ UInfixE (VarE 'lift) (VarE '(.)) (VarE $ mkName "liftStack"))
                            []
                        ]
                  _ -> []
          pure $ baseInstance : inductiveInstances
      _ -> pure []

mkIsStackOver :: Q [Dec]
mkIsStackOver =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        do
          m <- newName "m"
          n <- newName "n"
          let fName = mkName "IsStackOver"
          let mSig = ArrowT # StarT # StarT
              --   IsStackOver m m = True
              eqCase = TySynEqn Nothing (ConT fName # VarT m # VarT m) (PromotedT 'True)
              mtCases =
                instances
                  >>= \case
                    InstanceD _ _ (AppT (ConT _) t) _ ->
                      pure $
                        --   IsStackOver m (t n) = IsStackOver m n
                        TySynEqn
                          Nothing
                          (ConT fName # VarT m # (t # VarT n))
                          (ConT fName # VarT m # VarT n)
                    _ -> []

              --   IsStackOver _ _ = True
              defCase = TySynEqn Nothing (ConT fName # WildCardT # WildCardT) (PromotedT 'False)
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
