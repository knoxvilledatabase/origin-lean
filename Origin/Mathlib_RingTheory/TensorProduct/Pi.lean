/-
Extracted from RingTheory/TensorProduct/Pi.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor product and products of algebras

In this file we examine the behaviour of the tensor product with (finite) products. This
is a direct application of `Mathlib.LinearAlgebra.TensorProduct.Pi` to the algebra case.

-/

open TensorProduct

section

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring A]
  [Algebra R A] [Algebra S A] [IsScalarTower R S A]

variable {ι : Type*} (B : ι → Type*) [∀ i, CommSemiring (B i)] [∀ i, Algebra R (B i)]

@[simp]
lemma piRightHom_one : piRightHom R S A B 1 = 1 := rfl

variable {R S A B} in

@[simp]
lemma piRightHom_mul (x y : A ⊗[R] ∀ i, B i) :
    piRightHom R S A B (x * y) = piRightHom R S A B x * piRightHom R S A B y := by
  induction x
  · simp
  · induction y
    · simp
    · ext j
      simp
    · simp_all [mul_add]
  · simp_all [add_mul]

noncomputable def piRightHom : A ⊗[R] (∀ i, B i) →ₐ[S] ∀ i, A ⊗[R] B i :=
  AlgHom.ofLinearMap (_root_.TensorProduct.piRightHom R S A B) (by simp) (by simp)

variable [Fintype ι] [DecidableEq ι]

noncomputable def Algebra.TensorProduct.piRight :
    A ⊗[R] (∀ i, B i) ≃ₐ[S] ∀ i, A ⊗[R] B i :=
  AlgEquiv.ofLinearEquiv (_root_.TensorProduct.piRight R S A B) (by simp) (by simp)

@[simp]
lemma Algebra.TensorProduct.piRight_tmul (x : A) (f : ∀ i, B i) :
    piRight R S A B (x ⊗ₜ f) = (fun j ↦ x ⊗ₜ f j) := rfl

end
