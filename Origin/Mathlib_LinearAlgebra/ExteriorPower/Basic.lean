/-
Extracted from LinearAlgebra/ExteriorPower/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exterior powers

We study the exterior powers of a module `M` over a commutative ring `R`.

## Definitions

* `exteriorPower.ιMulti` is the canonical alternating map on `M` with values in `⋀[R]^n M`.

* `exteriorPower.presentation R n M` is the standard presentation of the `R`-module `⋀[R]^n M`.

* `exteriorPower.map n f : ⋀[R]^n M →ₗ[R] ⋀[R]^n N` is the linear map on `nth` exterior powers
  induced by a linear map `f : M →ₗ[R] N`. (See the file
  `Mathlib/Algebra/Category/ModuleCat/ExteriorPower.lean` for the corresponding functor
  `ModuleCat R ⥤ ModuleCat R`.)

## Theorems
* `exteriorPower.ιMulti_span`: The image of `exteriorPower.ιMulti` spans `⋀[R]^n M`.

* We construct `exteriorPower.alternatingMapLinearEquiv` which
  expresses the universal property of the exterior power as a
  linear equivalence `(M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] ⋀[R]^n M →ₗ[R] N` between
  alternating maps and linear maps from the exterior power.

-/

open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ) {M N N' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N']

namespace exteriorPower

open Function Set Set.powersetCard

/-! The canonical alternating map from `Fin n → M` to `⋀[R]^n M`. -/

def ιMulti : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M) :=
  (ExteriorAlgebra.ιMulti R n).codRestrict (⋀[R]^n M) fun _ =>
    ExteriorAlgebra.ιMulti_range R n <| Set.mem_range_self _
