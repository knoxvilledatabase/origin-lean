/-
Extracted from RingTheory/TensorProduct/Quotient.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Interaction between quotients and tensor products for algebras

This file proves algebra analogs of the isomorphisms in
`Mathlib/LinearAlgebra/TensorProduct/Quotient.lean`.

## Main results

- `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`:
  `B ⧸ (I.map <| algebraMap A B) ≃ₐ[B] B ⊗[A] (A ⧸ I)`
-/

open TensorProduct

namespace Algebra.TensorProduct

variable {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

set_option backward.privateInPublic true in

private noncomputable def quotIdealMapEquivTensorQuotAux :
      (B ⧸ (I.map <| algebraMap A B)) ≃ₗ[B] B ⊗[A] (A ⧸ I) :=
  AddEquiv.toLinearEquiv (TensorProduct.tensorQuotEquivQuotSMul B I ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv A (I.map <| algebraMap A B)).symm <| by
    intro c x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

noncomputable def quotIdealMapEquivTensorQuot :
    (B ⧸ (I.map <| algebraMap A B)) ≃ₐ[B] B ⊗[A] (A ⧸ I) :=
  AlgEquiv.ofLinearEquiv (quotIdealMapEquivTensorQuotAux B I) rfl
    (fun x y ↦ by
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp_rw [← map_mul, quotIdealMapEquivTensorQuotAux_mk]
      simp)
