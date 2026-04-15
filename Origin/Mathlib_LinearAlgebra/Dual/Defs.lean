/-
Extracted from LinearAlgebra/Dual/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.

## Main definitions

* Duals and transposes:
  * `Module.Dual R M` defines the dual space of the `R`-module `M`, as `M →ₗ[R] R`.
  * `Module.dualPairing R M` is the canonical pairing between `Dual R M` and `M`.
  * `Module.Dual.eval R M : M →ₗ[R] Dual R (Dual R)` is the canonical map to the double dual.
  * `Module.Dual.transpose` is the linear map from `M →ₗ[R] M'` to `Dual R M' →ₗ[R] Dual R M`.
  * `LinearMap.dualMap` is `Module.Dual.transpose` of a given linear map, for dot notation.
  * `LinearEquiv.dualMap` is for the dual of an equivalence.
* Submodules:
  * `Submodule.dualRestrict W` is the transpose `Dual R M →ₗ[R] Dual R W` of the inclusion map.
  * `Submodule.dualAnnihilator W` is the kernel of `W.dualRestrict`. That is, it is the submodule
    of `dual R M` whose elements all annihilate `W`.
  * `Submodule.dualPairing W` is the canonical pairing between `Dual R M ⧸ W.dualAnnihilator`
    and `W`. It is nondegenerate for vector spaces (`Subspace.dualPairing_nondegenerate`).

## Main results

* Annihilators:
  * `Module.dualAnnihilator_gc R M` is the antitone Galois correspondence between
    `Submodule.dualAnnihilator` and `Submodule.dualCoannihilator`.
* Finite-dimensional vector spaces:
  * `Module.evalEquiv` is the equivalence `V ≃ₗ[K] Dual K (Dual K V)`
  * `Module.mapEvalEquiv` is the order isomorphism between subspaces of `V` and
    subspaces of `Dual K (Dual K V)`.
-/

open Module Submodule

noncomputable section

namespace Module

variable (R A M : Type*)

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

abbrev Dual (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :=
  M →ₗ[R] R

def dualPairing (R M) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module.Dual R M →ₗ[R] M →ₗ[R] R :=
  LinearMap.id
