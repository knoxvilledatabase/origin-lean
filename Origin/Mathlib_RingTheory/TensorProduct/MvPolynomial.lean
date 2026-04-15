/-
Extracted from RingTheory/TensorProduct/MvPolynomial.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Tensor Product of (multivariate) polynomial rings

Let `Semiring R`, `Algebra R S` and `Module R N`.

* `MvPolynomial.rTensor` gives the linear equivalence
  `MvPolynomial σ S ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ (S ⊗[R] N)` characterized,
  for `p : MvPolynomial σ S`, `n : N` and `d : σ →₀ ℕ`, by
  `rTensor (p ⊗ₜ[R] n) d = (coeff d p) ⊗ₜ[R] n`
* `MvPolynomial.scalarRTensor` gives the linear equivalence
  `MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N`
  such that `MvPolynomial.scalarRTensor (p ⊗ₜ[R] n) d = coeff d p • n`
  for `p : MvPolynomial σ R`, `n : N` and `d : σ →₀ ℕ`, by

* `MvPolynomial.rTensorAlgHom`, the algebra morphism from the tensor product
  of a polynomial algebra by an algebra to a polynomial algebra
* `MvPolynomial.rTensorAlgEquiv`, `MvPolynomial.scalarRTensorAlgEquiv`,
  the tensor product of a polynomial algebra by an algebra
  is algebraically equivalent to a polynomial algebra

## TODO :
* `MvPolynomial.rTensor` could be phrased in terms of `AddMonoidAlgebra`, and
  `MvPolynomial.rTensor` then has `smul` by the polynomial algebra.
* `MvPolynomial.rTensorAlgHom` and `MvPolynomial.scalarRTensorAlgEquiv`
  are morphisms for the algebra structure by `MvPolynomial σ R`.
-/

universe u v

noncomputable section

namespace MvPolynomial

open DirectSum TensorProduct

open Set LinearMap Submodule

variable {R : Type u} {N : Type v} [CommSemiring R]

variable {σ ι : Type*}

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Module

variable [DecidableEq σ]

variable [AddCommMonoid N] [Module R N]

noncomputable def rTensor :
    MvPolynomial σ S ⊗[R] N ≃ₗ[S] (σ →₀ ℕ) →₀ (S ⊗[R] N) :=
  TensorProduct.finsuppLeft _ _ _ _ _

lemma rTensor_apply_tmul (p : MvPolynomial σ S) (n : N) :
    rTensor (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) :=
  TensorProduct.finsuppLeft_apply_tmul p n

lemma rTensor_apply_tmul_apply (p : MvPolynomial σ S) (n : N) (d : σ →₀ ℕ) :
    rTensor (p ⊗ₜ[R] n) d = (coeff d p) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_apply_tmul_apply p n d

lemma rTensor_apply_monomial_tmul (e : σ →₀ ℕ) (s : S) (n : N) (d : σ →₀ ℕ) :
    rTensor (monomial e s ⊗ₜ[R] n) d = if e = d then s ⊗ₜ[R] n else 0 := by
  simp only [rTensor_apply_tmul_apply, coeff_monomial, ite_tmul]

lemma rTensor_apply_X_tmul (s : σ) (n : N) (d : σ →₀ ℕ) :
    rTensor (X s ⊗ₜ[R] n) d = if Finsupp.single s 1 = d then (1 : S) ⊗ₜ[R] n else 0 := by
  rw [rTensor_apply_tmul_apply, coeff_X', ite_tmul]

lemma rTensor_apply (t : MvPolynomial σ S ⊗[R] N) (d : σ →₀ ℕ) :
    rTensor t d = ((lcoeff S d).restrictScalars R).rTensor N t :=
  TensorProduct.finsuppLeft_apply t d
