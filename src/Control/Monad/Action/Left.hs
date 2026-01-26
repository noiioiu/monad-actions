-- | Operators for left monad actions.
--   This module should be imported qualified, and can be used with the @QualifiedDo@ extension.
module Control.Monad.Action.Left
  ( (>>=),
    (>>),
    (=<<),
    (>=>),
    (<=<),
    (<*>),
    fmap,
    pure,
    return,
    fail,
    join,
    mfix,
  )
where

import Control.Monad.Action
import Control.Monad.Fix qualified as F
import Prelude hiding (fail, fmap, pure, return, (<*>), (=<<), (>>), (>>=))
import Prelude qualified as P

infixl 1 >>=

-- | @'lbind'@ in operator form.
(>>=) :: (LeftModule m f) => m a -> (a -> f b) -> f b
(>>=) = lbind

infixr 1 =<<

-- | @'lbind'@ with arguments swapped.
(=<<) :: (LeftModule m f) => (a -> f b) -> m a -> f b
(=<<) = flip lbind

infixl 1 >>

(>>) :: (LeftModule m f) => m a -> f b -> f b
(>>) = (. const) . lbind

infixr 1 >=>

(>=>) :: (LeftModule m f) => (a -> m b) -> (b -> f c) -> a -> f c
(>=>) = flip $ (.) . (=<<)

infixr 1 <=<

(<=<) :: (LeftModule m f) => (b -> f c) -> (a -> m b) -> a -> f c
(<=<) = (.) . (=<<)

-- | Alias for @'ljoin'@.
join :: (LeftModule m f) => m (f a) -> f a
join = ljoin

-- | Re-export from "Prelude".
fmap :: (Functor f) => (a -> b) -> f a -> f b
fmap = P.fmap

-- | Re-export from "Prelude".
pure :: (Applicative f) => a -> f a
pure = P.pure

-- | Re-export from "Prelude".
fail :: (MonadFail m) => String -> m a
fail = P.fail

-- | Re-export from "Control.Monad.Fix".
mfix :: (F.MonadFix m) => (a -> m a) -> m a
mfix = F.mfix

-- | Alias for @'pure'@.
return :: (Applicative f) => a -> f a
return = pure

infixl 4 <*>

-- | Used for desugaring qualified @do@ blocks when @ApplicativeDo@ is enabled.
(<*>) :: (LeftModule m f) => m (a -> b) -> f a -> f b
fs <*> xs = fs >>= flip fmap xs
