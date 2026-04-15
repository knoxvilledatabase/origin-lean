/-
Extracted from Data/Finsupp/Weight.lean
Genuine: 9 of 17 | Dissolved: 6 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # weights of Finsupp functions

The theory of multivariate polynomials and power series is built
on the type `σ →₀ ℕ` which gives the exponents of the monomials.
Many aspects of the theory (degree, order, graded ring structure)
require to classify these exponents according to their total sum
`∑  i, f i`, or variants, and this files provides some API for that.

## Weight

We fix a type `σ` and an `AddCommMonoid M`, as well as a function `w : σ → M`.

- `Finsupp.weight` of a finitely supported function `f : σ →₀ ℕ`
with respect to `w`: it is the sum `∑ (f i) • (w i)`.
It is an `AddMonoidHom` map defined using `Finsupp.linearCombination`.

- `Finsupp.le_weight`says that `f s ≤ f.weight w` when `M = ℕ``

- `Finsupp.le_weight_of_nonneg'` says that `w s ≤ f.weight w`
for `OrderedAddCommMonoid M`, when `f s ≠ 0` and all `w i` are nonnegative.

- `Finsupp.le_weight'` is the same statement for `CanonicallyOrderedAddCommMonoid M`.

- `NonTorsionWeight`: all values `w s` are non torsion in `M`.

- `Finsupp.weight_eq_zero_iff_eq_zero` says that `f.weight w = 0` iff
`f = 0` for `NonTorsion Weight w` and `CanonicallyOrderedAddCommMonoid M`.

- For `w : σ → ℕ` and `Finite σ`, `Finsupp.finite_of_nat_weight_le` proves that
there are finitely many `f : σ →₀ ℕ` of bounded weight.

## Degree

- `Finsupp.degree`:  the weight when all components of `w` are equal to `1 : ℕ`.
The present choice is to have it defined as a plain function.

- `Finsupp.degree_eq_zero_iff` says that `f.degree = 0` iff `f = 0`.

- `Finsupp.le_degree` says that `f s ≤ f.degree`.

- `Finsupp.degree_eq_weight_one` says `f.degree = f.weight 1`.
This is useful to access the additivity properties of `Finsupp.degree`

- For `Finite σ`, `Finsupp.finite_of_degree_le` proves that
there are finitely many `f : σ →₀ ℕ` of bounded degree.



## TODO

* The relevant generality of these constructions is not clear.
It could probably be generalized to `w : σ → M` and `f : σ →₀ N`,
provided `N` is a commutative semiring and `M`is an `N`-module.

* Maybe `Finsupp.weight w` and `Finsupp.degree` should have similar types,
both `AddCommMonoidHom` or both functions.

-/

variable {σ M : Type*} (w : σ → M)

namespace Finsupp

section AddCommMonoid

variable [AddCommMonoid M]

noncomputable def weight : (σ →₀ ℕ) →+ M :=
  (Finsupp.linearCombination ℕ w).toAddMonoidHom

alias _root_.MvPolynomial.weightedDegree := weight

theorem weight_apply (f : σ →₀ ℕ) :
    weight w f = Finsupp.sum f (fun i c => c • w i) := rfl

alias _root_.MvPolynomial.weightedDegree_apply := weight_apply

class NonTorsionWeight (w : σ → M) : Prop where
  eq_zero_of_smul_eq_zero {n : ℕ} {s : σ} (h : n • w s = 0)  : n = 0

-- DISSOLVED: nonTorsionWeight_of

-- DISSOLVED: NonTorsionWeight.ne_zero

end AddCommMonoid

section OrderedAddCommMonoid

-- DISSOLVED: le_weight

variable [OrderedAddCommMonoid M] (w : σ → M)

instance : SMulPosMono ℕ M :=
  ⟨fun b hb m m' h ↦ by
    rw [← Nat.add_sub_of_le h, add_smul]
    exact le_add_of_nonneg_right (nsmul_nonneg hb (m' - m))⟩

variable {w} in

-- DISSOLVED: le_weight_of_ne_zero

end OrderedAddCommMonoid

section CanonicallyOrderedAddCommMonoid

variable {M : Type*} [CanonicallyOrderedAddCommMonoid M] (w : σ → M)

-- DISSOLVED: le_weight_of_ne_zero'

theorem weight_eq_zero_iff_eq_zero
    (w : σ → M) [NonTorsionWeight w] {f : σ →₀ ℕ} :
    weight w f = 0 ↔ f = 0 := by
  classical
  constructor
  · intro h
    ext s
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hs
    apply NonTorsionWeight.ne_zero w s
    rw [← nonpos_iff_eq_zero, ← h]
    exact le_weight_of_ne_zero' w hs
  · intro h
    rw [h, map_zero]

-- DISSOLVED: finite_of_nat_weight_le

end CanonicallyOrderedAddCommMonoid

def degree (d : σ →₀ ℕ) := ∑ i ∈ d.support, d i

alias _root_.MvPolynomial.degree := degree

lemma degree_eq_zero_iff (d : σ →₀ ℕ) : degree d = 0 ↔ d = 0 := by
  simp only [degree, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, ne_eq, Decidable.not_imp_self,
    DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply]

alias _root_.MvPolynomial.degree_eq_zero_iff := degree_eq_zero_iff

@[simp]
theorem degree_zero : degree (0 : σ →₀ ℕ) = 0 := by rw [degree_eq_zero_iff]

theorem degree_eq_weight_one :
    degree (σ := σ) = weight 1 := by
  ext d
  simp only [degree, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum]

alias _root_.MvPolynomial.weightedDegree_one := degree_eq_weight_one

theorem le_degree (s : σ) (f : σ →₀ ℕ) : f s ≤ degree f  := by
  rw [degree_eq_weight_one]
  apply le_weight
  simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true]

theorem finite_of_degree_le [Finite σ] (n : ℕ) :
    {f : σ →₀ ℕ | degree f ≤ n}.Finite := by
  simp_rw [degree_eq_weight_one]
  refine finite_of_nat_weight_le (Function.const σ 1) ?_ n
  intro _
  simp only [Function.const_apply, ne_eq, one_ne_zero, not_false_eq_true]

end Finsupp
