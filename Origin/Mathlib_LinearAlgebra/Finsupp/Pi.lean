/-
Extracted from LinearAlgebra/Finsupp/Pi.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Properties of the module `α →₀ M`

* `Finsupp.linearEquivFunOnFinite`: `α →₀ β` and `a → β` are equivalent if `α` is finite
* `FunOnFinite.map`: the map `(X → M) → (Y → M)` induced by a map `f : X ⟶ Y` when
  `X` and `Y` are finite.
* `FunOnFinite.linearMmap`: the linear map `(X → M) →ₗ[R] (Y → M)` induced
  by a map `f : X ⟶ Y` when `X` and `Y` are finite.

## Tags

function with finite support, module, linear algebra
-/

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

section LinearEquiv.finsuppUnique

variable (R : Type*) {S : Type*} (M : Type*)

variable [AddCommMonoid M] [Semiring R] [Module R M]

variable (α : Type*) [Unique α]

noncomputable def LinearEquiv.finsuppUnique : (α →₀ M) ≃ₗ[R] M :=
  { Finsupp.equivFunOnFinite.trans (Equiv.funUnique α M) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable {R M}
