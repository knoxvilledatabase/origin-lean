/-
Extracted from RingTheory/AdicCompletion/Functoriality.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functoriality of adic completions

In this file we establish functorial properties of the adic completion.

## Main definitions

- `AdicCauchySequence.map I f`: the linear map on `I`-adic Cauchy sequences induced by `f`
- `AdicCompletion.map I f`: the linear map on `I`-adic completions induced by `f`

## Main results

- `sumEquivOfFintype`: adic completion commutes with finite sums
- `piEquivOfFintype`: adic completion commutes with finite products

-/

suppress_compilation

variable {R : Type*} [CommRing R] (I : Ideal R)

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {N : Type*} [AddCommGroup N] [Module R N]

variable {P : Type*} [AddCommGroup P] [Module R P]

variable {T : Type*} [AddCommGroup T] [Module (AdicCompletion I R) T]

namespace LinearMap

set_option backward.privateInPublic true in

private def reduceModIdealAux (f : M →ₗ[R] N) :
    M ⧸ (I • ⊤ : Submodule R M) →ₗ[R] N ⧸ (I • ⊤ : Submodule R N) :=
  Submodule.mapQ (I • ⊤ : Submodule R M) (I • ⊤ : Submodule R N) f
    (fun x hx ↦ by
      refine Submodule.smul_induction_on hx (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ ?_)
      · simp [Submodule.smul_mem_smul hr Submodule.mem_top]
      · simp [Submodule.add_mem _ hx hy])
