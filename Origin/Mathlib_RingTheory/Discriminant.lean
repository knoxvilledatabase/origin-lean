/-
Extracted from RingTheory/Discriminant.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Discriminant of a family of vectors

Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define the
*discriminant* of `b` as the determinant of the matrix whose `(i j)`-th element is the trace of
`b i * b j`.

## Main definition

* `Algebra.discr A b` : the discriminant of `b : ι → B`.

## Main results

* `Algebra.discr_zero_of_not_linearIndependent` : if `b` is not linear independent, then
  `Algebra.discr A b = 0`.
* `Algebra.discr_of_matrix_vecMul` and `Algebra.discr_of_matrix_mulVec` : formulas relating
  `Algebra.discr A ι b` with `Algebra.discr A (b ᵥ* P.map (algebraMap A B))` and
  `Algebra.discr A (P.map (algebraMap A B) *ᵥ b)`.
* `Algebra.discr_not_zero_of_basis` : over a field, if `b` is a basis, then
  `Algebra.discr K b ≠ 0`.
* `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two` : if `L/K` is a field extension and
  `b : ι → L`, then `discr K b` is the square of the determinant of the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the embedding in an algebraically closed
  field `E` corresponding to `j : ι` via a bijection `e : ι ≃ (L →ₐ[K] E)`.
* `Algebra.discr_powerBasis_eq_prod` : the discriminant of a power basis.
* `Algebra.discr_isIntegral` : if `K` and `L` are fields and `IsScalarTower R K L`, if
  `b : ι → L` satisfies `∀ i, IsIntegral R (b i)`, then `IsIntegral R (discr K b)`.
* `Algebra.discr_mul_isIntegral_mem_adjoin` : let `K` be the fraction field of an integrally
  closed domain `R` and let `L` be a finite separable extension of `K`. Let `B : PowerBasis K L`
  be such that `IsIntegral R B.gen`. Then for all, `z : L` we have
  `(discr K B.basis) • z ∈ adjoin R ({B.gen} : Set L)`.

## Implementation details

Our definition works for any `A`-algebra `B`, but note that if `B` is not free as an `A`-module,
then `trace A B = 0` by definition, so `discr A b = 0` for any `b`.
-/

universe u v w z

open scoped Matrix

open Matrix Module Fintype Polynomial Finset IntermediateField

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z) {ι : Type w} [DecidableEq ι]

variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

section Discr

noncomputable def discr (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] (b : ι → B) := (traceMatrix A b).det

variable {A C} in

theorem discr_eq_discr_of_algEquiv [Fintype ι] (b : ι → B) (f : B ≃ₐ[A] C) :
    Algebra.discr A b = Algebra.discr A (f ∘ b) := by
  rw [discr_def]; congr; ext
  simp_rw [traceMatrix_apply, traceForm_apply, Function.comp, ← map_mul f, trace_eq_of_algEquiv]

variable {ι' : Type*} [Fintype ι'] [Fintype ι] [DecidableEq ι']

section Basic
