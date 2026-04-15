/-
Extracted from CategoryTheory/Monad/Kleisli.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Kleisli category on a (co)monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)` as well as the co-Kleisli
category on a comonad `(U, ε_ U, δ_ U)`. It also defines the Kleisli adjunction which gives rise to
the monad `(T, η_ T, μ_ T)` as well as the co-Kleisli adjunction which gives rise to the comonad
`(U, ε_ U, δ_ U)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

structure Kleisli (T : Monad C) where mk (T) ::
  /-- The underlying object of the base category. -/
  of : C

namespace Kleisli

variable {T : Monad C}
