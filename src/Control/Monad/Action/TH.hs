{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeData #-}

module Control.Monad.Action.TH (mkLiftBy) where

import Control.Monad.Trans
import Data.Kind qualified as K
import Language.Haskell.TH

infixl 5 #

(#) :: Type -> Type -> Type
(#) = AppT

(|->|) :: Type -> Type -> Type
a |->| b = ArrowT # a # b

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
                      [ KindedTV m BndrReq (StarT |->| StarT),
                        KindedTV n BndrReq (StarT |->| StarT)
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
                        (ct ++ [ConT (mkName "LiftBy") # VarT k # VarT m # VarT n])
                        (ConT (mkName "LiftBy") # (ConT (mkName "S") # VarT k) # VarT m # (t # VarT n))
                        [ ValD
                            (VarP $ mkName "liftBy")
                            (NormalB $ UInfixE (VarE 'lift) (VarE '(.)) (AppTypeE (VarE $ mkName "liftBy") (VarT k)))
                            []
                        ]
                  _ -> []
          pure $ decs ++ famDec : inductiveInstances
      _ -> pure []
