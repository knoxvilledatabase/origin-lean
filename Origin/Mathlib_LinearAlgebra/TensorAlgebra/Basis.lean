/-
Extracted from LinearAlgebra/TensorAlgebra/Basis.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# A basis for `TensorAlgebra R M`

## Main definitions

* `TensorAlgebra.equivMonoidAlgebra b : TensorAlgebra R M ≃ₐ[R] FreeAlgebra R κ`:
  the isomorphism given by a basis `b : Basis κ R M`.
* `Basis.tensorAlgebra b : Basis (FreeMonoid κ) R (TensorAlgebra R M)`:
  the basis on the tensor algebra given by a basis `b : Basis κ R M`.

## Main results

* `TensorAlgebra.instFreeModule`: the tensor algebra over `M` is free when `M` is
* `TensorAlgebra.rank_eq`

-/

open Module

namespace TensorAlgebra

universe uκ uR uM

variable {κ : Type uκ} {R : Type uR} {M : Type uM}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

noncomputable def equivFreeAlgebra (b : Basis κ R M) :
    TensorAlgebra R M ≃ₐ[R] FreeAlgebra R κ :=
  AlgEquiv.ofAlgHom
    (TensorAlgebra.lift _ (Finsupp.linearCombination _ (FreeAlgebra.ι _) ∘ₗ b.repr.toLinearMap))
    (FreeAlgebra.lift _ (ι R ∘ b))
    (by ext; simp)
    (hom_ext <| b.ext fun i => by simp)
