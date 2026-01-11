-- | Given a monad \(M\) on a category \(\mathcal{D}\) with unit \(\eta\) and
--     multiplication \(\mu\) and a functor \(F\) from \(\mathcal{C}\) to \(\mathcal{D}\),
--     a left monad action of \(M\) on \(F\) is a natural transformation \(\nu\) such that
--     the following two laws hold:
--
--     * \(\nu \cdot (\eta \circ F) = \mathrm{id}_F\)
--     * \(\nu \cdot (\mu \circ F) = \nu \cdot (M \circ \nu)\)
--
--     We also say that \(F\) is a left module over \(M\).  In the case
--     \(\mathcal{C} = \mathcal{D}\), a left monad module is a left monoid module
--     object in the category of endofunctors on \(\mathcal{C}\).  We may also
--     call \(\alpha\) the scalar multiplication of the module by the monad, by analogy
--     with ring modules, which are monoid module objects in the category of abelian groups
--     with tensor product as the monoidal product (rings are just monoid objects in this
--     category).
--
--     Right monad actions are defined similarly.
--
--     See [this blog post](https://stringdiagram.com/2023/04/23/monad-actions/) by Dan Marsden
--     or the paper /Modules over monads and their algebras/ by Piróg, Wu, and Gibbons.
module Control.Monad.Action
  ( module C,
  )
where

import Control.Monad.Action.Class as C
import Control.Monad.Action.Instances ()
