/-
Extracted from LinearAlgebra/SymmetricAlgebra/Basis.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# A basis for `SymmetricAlgebra R M`

## Main definitions

* `SymmetricAlgebra.equivMvPolynomial b : SymmetricAlgebra R M ≃ₐ[R] MvPolynomial I R`:
  the isomorphism given by a basis `b : Basis I R M`.
* `Basis.symmetricAlgebra b : Basis (I →₀ ℕ) R (SymmetricAlgebra R M)`:
  the basis on the symmetric algebra given by a basis `b : Basis I R M`.

## Main results

* `SymmetricAlgebra.instFreeModule`: the symmetric algebra over `M` is free when `M` is free.
* `SymmetricAlgebra.rank_eq`: the rank of `SymmetricAlgebra R M` when `M` is a nontrivial free
  module is equal to `max (Module.rank R M) Cardinal.aleph0`.

## Implementation notes

This file closely mirrors the corresponding file for `TensorAlgebra`.
-/

open Module

namespace SymmetricAlgebra

universe uκ uR uM

variable {κ : Type uκ} {R : Type uR} {M : Type uM}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

noncomputable def equivMvPolynomial (b : Basis κ R M) :
    SymmetricAlgebra R M ≃ₐ[R] MvPolynomial κ R :=
  .ofAlgHom
    (SymmetricAlgebra.lift <| Basis.constr b R .X)
    (MvPolynomial.aeval fun i ↦ ι R M (b i))
    (MvPolynomial.algHom_ext fun i ↦ by simp)
    (algHom_ext <| b.ext fun i ↦ by simp)
