{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Control.Monad.Action.TH (mkLiftStackInstances) where

import Control.Monad.Trans
import Language.Haskell.TH

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
                  (Just Incoherent)
                  []
                  (ConT cName # VarT m # VarT m)
                  [ValD (VarP $ mkName "liftStack") (NormalB $ VarE 'id) []]
              inductiveInstances =
                instances >>= \case
                  InstanceD _ ct (AppT (ConT _) t) _ ->
                    -- instance (Monad m, Monad n, LiftStack m n) => LiftStack m (t n) where
                    --   liftStack = lift . liftStack
                    pure $
                      InstanceD
                        (Just Incoherent)
                        ( [ ConT ''Monad # VarT m,
                            ConT ''Monad # VarT n,
                            ConT cName # VarT m # VarT n
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
