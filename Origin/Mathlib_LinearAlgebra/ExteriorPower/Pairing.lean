/-
Extracted from LinearAlgebra/ExteriorPower/Pairing.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The pairing between the exterior power of the dual and the exterior power

We construct the pairing
`exteriorPower.pairingDual : ⋀[R]^n (Module.Dual R M) →ₗ[R] (Module.Dual R (⋀[R]^n M))`.

-/

namespace exteriorPower

open TensorProduct PiTensorProduct

variable (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def toTensorPower (n : ℕ) : ⋀[R]^n M →ₗ[R] ⨂[R]^n M :=
  alternatingMapLinearEquiv (MultilinearMap.alternatization (PiTensorProduct.tprod R))

variable {M} in

open Equiv in
