/-
Extracted from Topology/Homeomorph/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homeomorphisms

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

## Main definitions and results

* `Homeomorph X Y`: The type of homeomorphisms from `X` to `Y`.
  This type can be denoted using the following notation: `X ≃ₜ Y`.
* `HomeomorphClass`: `HomeomorphClass F A B` states that `F` is a type of homeomorphisms.

* `Homeomorph.symm`: the inverse of a homeomorphism
* `Homeomorph.trans`: composing two homeomorphisms
* Homeomorphisms are open and closed embeddings, inducing, quotient maps etc.
* `Homeomorph.homeomorphOfContinuousOpen`: A continuous bijection that is
  an open map is a homeomorphism.
* `Homeomorph.homeomorphOfUnique`: if both `X` and `Y` have a unique element, then `X ≃ₜ Y`.
* `Equiv.toHomeomorph`: an equivalence between topological spaces respecting openness
  is a homeomorphism.

* `IsHomeomorph`: the predicate that a function is a homeomorphism

-/

open Set Topology Filter

variable {X Y W Z : Type*}

structure Homeomorph (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map of a homeomorphism is a continuous function. -/
  continuous_toFun : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp -failIfUnchanged; fun_prop
  /-- The inverse map of a homeomorphism is a continuous function. -/
  continuous_invFun : Continuous invFun := by
    first | fun_prop | eta_expand; dsimp -failIfUnchanged; fun_prop
