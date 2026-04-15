/-
Extracted from LinearAlgebra/PiTensorProduct/Dual.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor products of dual spaces

## Main definitions

* `PiTensorProduct.dualDistrib`: The canonical linear map from `⨂[R] i, Dual R (M i)` to
  `Dual R (⨂[R] i, M i)`, sending `⨂ₜ[R] i, f i` to the composition of
  `PiTensorProduct.map f` with the linear equivalence `⨂[R] i, R →ₗ R` given by multiplication.

* `PiTensorProduct.dualDistribEquiv`: A linear equivalence between `⨂[R] i, Dual R (M i)`
  and `Dual R (⨂[R] i, M i)` when all `M i` are finite free modules. If
  `f : (i : ι) → Dual R (M i)`, then this equivalence sends `⨂ₜ[R] i, f i` to the composition of
  `PiTensorProduct.map f` with the natural isomorphism `⨂[R] i, R ≃ R` given by multiplication.
-/

namespace PiTensorProduct

open PiTensorProduct LinearMap Module TensorProduct

variable {ι : Type*}

section SemiRing

variable {R : Type*} {M : ι → Type*} [CommSemiring R] [Π i, AddCommMonoid (M i)]
  [Π i, Module R (M i)]

noncomputable def dualDistrib [Finite ι] : (⨂[R] i, Dual R (M i)) →ₗ[R] Dual R (⨂[R] i, M i) :=
  haveI := Fintype.ofFinite ι
  (LinearMap.compRight _ (constantBaseRingEquiv ι R).toLinearMap) ∘ₗ piTensorHomMap
