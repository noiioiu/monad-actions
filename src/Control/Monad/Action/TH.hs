{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeData #-}

module Control.Monad.Action.TH (mkLiftBy, mkWriterActions) where

import Control.Monad (join)
import Control.Monad.Trans
import Control.Monad.Writer.Class (MonadWriter (..))
import Data.Kind qualified as K
import Language.Haskell.TH

infixl 5 #

(#) :: Type -> Type -> Type
(#) = AppT

(|->|) :: Type -> Type -> Type
a |->| b = ArrowT # a # b

mkWriterActions :: Q [Dec]
mkWriterActions =
  reify (mkName "IsWriter")
    >>= \case
      ClassI _ instances -> do
        f <- newName "f"
        a <- newName "a"
        g <- newName "g"
        let leftmoduleDecs =
              instances >>= \case
                InstanceD _ ct (AppT (AppT _IsWriter w) m) _ ->
                  pure $
                    InstanceD
                      (Just Incoherent)
                      ((ConT ''MonadWriter # w # VarT f) : ct)
                      (ConT (mkName "LeftModule") # m # VarT f)
                      [ ValD
                          (VarP $ mkName "ljoin")
                          (NormalB . UInfixE (VarE 'join) (VarE '(.)) $ UInfixE (VarE 'writer) (VarE '(.)) (VarE $ mkName "runWriter"))
                          [],
                        FunD
                          (mkName "lbind")
                          [ Clause
                              [VarP a, VarP g]
                              (NormalB $ UInfixE (AppE (VarE 'writer) (AppE (VarE $ mkName "runWriter") (VarE a))) (VarE '(>>=)) (VarE g))
                              []
                          ]
                      ]
                _ -> []
        let rightmoduleDecs =
              instances >>= \case
                InstanceD _ ct (AppT (AppT _IsWriter w) m) _ ->
                  pure $
                    InstanceD
                      (Just Incoherent)
                      ((ConT ''MonadWriter # w # VarT f) : ct)
                      (ConT (mkName "RightModule") # m # VarT f)
                      [ ValD
                          (VarP $ mkName "rjoin")
                          (NormalB . InfixE Nothing (VarE '(>>=)) . Just . UInfixE (VarE 'writer) (VarE '(.)) . VarE $ mkName "runWriter")
                          [],
                        FunD
                          (mkName "rbind")
                          [ Clause
                              [VarP a, VarP g]
                              (NormalB $ UInfixE (VarE a) (VarE '(>>=)) $ UInfixE (VarE 'writer) (VarE '(.)) $ UInfixE (VarE $ mkName "runWriter") (VarE '(.)) (VarE g))
                              []
                          ]
                      ]
                _ -> []
        let bimoduleDecs =
              do
                InstanceD _ ct (AppT (AppT _IsWriter w) m) _ <- instances
                InstanceD _ ct' (AppT (AppT _IsWriter w') n) _ <- instances
                pure $
                  InstanceD
                    (Just Incoherent)
                    ((ConT ''MonadWriter # w # VarT f) : (ConT ''MonadWriter # w' # VarT f) : ct ++ ct')
                    (ConT (mkName "BiModule") # m # n # VarT f)
                    []
        pure $ leftmoduleDecs ++ rightmoduleDecs ++ bimoduleDecs
      _ -> pure []

mkLiftBy :: Q [Dec]
mkLiftBy =
  reify ''MonadTrans
    >>= \case
      ClassI _ instances ->
        do
          decs <-
            [d|
              type data Nat = Z | S Nat

              class (Monad m, Monad n) => LiftBy (k :: Nat) (m :: K.Type -> K.Type) (n :: K.Type -> K.Type) | k n -> m where
                liftBy :: m a -> n a

              instance (Monad m) => LiftBy Z m m where
                liftBy = id
              |]
          let famName = mkName "Steps"
          m <- newName "m"
          n <- newName "n"
          k <- newName "k"
          let famDec =
                ClosedTypeFamilyD
                  ( TypeFamilyHead
                      famName
                      [ KindedTV m BndrReq (ConT ''K.Type |->| ConT ''K.Type),
                        KindedTV n BndrReq (ConT ''K.Type |->| ConT ''K.Type)
                      ]
                      (KindSig . ConT $ mkName "Nat")
                      Nothing
                  )
                  $ TySynEqn Nothing (ConT famName # VarT m # VarT m) (ConT $ mkName "Z")
                    : ( instances >>= \case
                          InstanceD _ _ (AppT (ConT _) t) _ ->
                            [ TySynEqn
                                Nothing
                                (ConT famName # VarT m # (t # VarT n))
                                (ConT (mkName "S") # (ConT famName # VarT m # VarT n))
                            ]
                          _ -> []
                      )
          let inductiveInstances =
                instances >>= \case
                  InstanceD ov ct (AppT (ConT _) t) _ ->
                    pure $
                      InstanceD
                        ov
                        (ct ++ [ConT (mkName "LiftBy") # VarT k # VarT m # VarT n, ConT ''Monad # (t # VarT n)])
                        (ConT (mkName "LiftBy") # (ConT (mkName "S") # VarT k) # VarT m # (t # VarT n))
                        [ ValD
                            (VarP $ mkName "liftBy")
                            (NormalB $ UInfixE (VarE 'lift) (VarE '(.)) (AppTypeE (VarE $ mkName "liftBy") (VarT k)))
                            []
                        ]
                  _ -> []
          pure $ decs ++ famDec : inductiveInstances
      _ -> pure []
