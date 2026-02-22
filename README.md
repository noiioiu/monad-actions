Left or right actions of a monad on a functor.

See [this blog post](https://stringdiagram.com/2023/04/23/monad-actions/) by Dan Marsden for an introduction to monad actions.

This package provides two implementations of monad actions.
The simpler one uses the `LeftModule`, `RightModule`, and `BiModule` classes defined in `Control.Monad.Action`,
and can be used with the `QualifiedDo` extension by qualifying the `do` blocks with either `Control.Monad.Action.Right` or `Control.Monad.Action.Left`.
However, it uses incoherent instances.
The second implementation, designed to avoid incoherent and overlapping instances, is defined in `Control.Monad.Action.Records`, and uses the `LeftAction`, `RightAtion`, and `BiAction` types.
It is meant to be used with `RecordWildCards` and `RebindableSyntax` and/or `OverloadedRecordDot`.
