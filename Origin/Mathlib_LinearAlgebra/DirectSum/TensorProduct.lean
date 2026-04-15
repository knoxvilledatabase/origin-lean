/-
Extracted from LinearAlgebra/DirectSum/TensorProduct.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor products of direct sums

This file shows that taking `TensorProduct`s commutes with taking `DirectSum`s in both arguments.

## Main results

* `TensorProduct.directSum`
* `TensorProduct.directSumLeft`
* `TensorProduct.directSumRight`
-/

universe u v₁ v₂ w₁ w₁' w₂ w₂'

section Ring

namespace TensorProduct

open TensorProduct

open DirectSum

open LinearMap

attribute [local ext] TensorProduct.ext

variable (R : Type u) [CommSemiring R] (S) [Semiring S] [Algebra R S]

variable {ι₁ : Type v₁} {ι₂ : Type v₂}

variable [DecidableEq ι₁] [DecidableEq ι₂]

variable (M₁ : ι₁ → Type w₁) (M₁' : Type w₁') (M₂ : ι₂ → Type w₂) (M₂' : Type w₂')

variable [∀ i₁, AddCommMonoid (M₁ i₁)] [AddCommMonoid M₁']

variable [∀ i₂, AddCommMonoid (M₂ i₂)] [AddCommMonoid M₂']

variable [∀ i₁, Module R (M₁ i₁)] [Module R M₁'] [∀ i₂, Module R (M₂ i₂)] [Module R M₂']

variable [∀ i₁, Module S (M₁ i₁)] [∀ i₁, IsScalarTower R S (M₁ i₁)]

variable [Module S M₁'] [IsScalarTower R S M₁']

protected def directSum :
    ((⨁ i₁, M₁ i₁) ⊗[R] ⨁ i₂, M₂ i₂) ≃ₗ[S] ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2 := by
  refine LinearEquiv.ofLinear ?toFun ?invFun ?left ?right
  · exact AlgebraTensorModule.lift <|
      toModule S _ _ fun i₁ => flip <| toModule R _ _ fun i₂ => flip <| AlgebraTensorModule.curry <|
      DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂)
  · exact toModule S _ _ fun i => AlgebraTensorModule.map (lof S _ M₁ i.1) (lof R _ M₂ i.2)
  · ext ⟨i₁, i₂⟩ x₁ x₂ : 4
    simp only [coe_comp, Function.comp_apply, toModule_lof, AlgebraTensorModule.map_tmul,
      AlgebraTensorModule.lift_apply, lift.tmul, coe_restrictScalars, flip_apply,
      AlgebraTensorModule.curry_apply, curry_apply, id_comp]
  · ext i₁ i₂ x₁ x₂ : 5
    simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
      coe_restrictScalars, AlgebraTensorModule.lift_apply, lift.tmul, toModule_lof, flip_apply,
      AlgebraTensorModule.map_tmul, id_coe, id_eq]

def directSumLeft : (⨁ i₁, M₁ i₁) ⊗[R] M₂' ≃ₗ[S] ⨁ i, M₁ i ⊗[R] M₂' :=
  TensorProduct.AlgebraTensorModule.congr 1 (DirectSum.lid _ _).symm ≪≫ₗ
  TensorProduct.directSum R S M₁ (fun _ : Unit ↦ M₂') ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.prodUnique _ _)

def directSumRight : (M₁' ⊗[R] ⨁ i, M₂ i) ≃ₗ[S] ⨁ i, M₁' ⊗[R] M₂ i :=
  TensorProduct.AlgebraTensorModule.congr (DirectSum.lid _ _).symm 1 ≪≫ₗ
  TensorProduct.directSum R S (fun _ : Unit ↦ M₁') M₂ ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.uniqueProd _ _)
