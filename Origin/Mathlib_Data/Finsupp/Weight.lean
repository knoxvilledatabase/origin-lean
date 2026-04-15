/-
Extracted from Data/Finsupp/Weight.lean
Genuine: 7 of 15 | Dissolved: 7 | Infrastructure: 1
-/
import Origin.Core

/-! # weights of Finsupp functions

The theory of multivariate polynomials and power series is built
on the type `σ →₀ ℕ` which gives the exponents of the monomials.
Many aspects of the theory (degree, order, graded ring structure)
require classifying these exponents according to their total sum
`∑ i, f i`, or variants, and this file provides some API for that.

## Weight

We fix a type `σ`, a semiring `R`, an `R`-module `M`,
as well as a function `w : σ → M`. (The important case is `R = ℕ`.)

- `Finsupp.weight` of a finitely supported function `f : σ →₀ R`
  with respect to `w`: it is the sum `∑ (f i) • (w i)`.
  It is an `AddMonoidHom` map defined using `Finsupp.linearCombination`.

- `Finsupp.le_weight` says that `f s ≤ f.weight w` when `M = ℕ`

- `Finsupp.le_weight_of_ne_zero` says that `w s ≤ f.weight w`
  for `OrderedAddCommMonoid M`, when `f s ≠ 0` and all `w i` are nonnegative.

- `Finsupp.le_weight_of_ne_zero'` is the same statement for `CanonicallyOrderedAddCommMonoid M`.

- `NonTorsionWeight`: all values `w s` are nontorsion in `M`.

- `Finsupp.weight_eq_zero_iff_eq_zero` says that `f.weight w = 0` iff
  `f = 0` for `NonTorsionWeight w` and `CanonicallyOrderedAddCommMonoid M`.

- For `w : σ → ℕ` and `Finite σ`, `Finsupp.finite_of_nat_weight_le` proves that
  there are finitely many `f : σ →₀ ℕ` of bounded weight.

## Degree

- `Finsupp.degree f` is the sum of all `f s`, for `s ∈ f.support`.
  The present choice is to have it defined as a plain function.

- `Finsupp.degree_eq_zero_iff` says that `f.degree = 0` iff `f = 0`.

- `Finsupp.le_degree` says that `f s ≤ f.degree`.

- `Finsupp.degree_eq_weight_one` says `f.degree = f.weight 1` when `R` is a semiring.
  This is useful to access the additivity properties of `Finsupp.degree`

- For `Finite σ`, `Finsupp.finite_of_degree_le` proves that
  there are finitely many `f : σ →₀ ℕ` of bounded degree.


## TODO

* Maybe `Finsupp.weight w` and `Finsupp.degree` should have similar types,
  both `AddMonoidHom` or both functions.

-/

open Module

variable {σ M R : Type*} [Semiring R] (w : σ → M)

namespace Finsupp

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]

noncomputable def weight : (σ →₀ R) →+ M :=
  (Finsupp.linearCombination R w).toAddMonoidHom

theorem weight_single_index [DecidableEq σ] (s : σ) (c : M) (f : σ →₀ R) :
    weight (Pi.single s c) f = f s • c :=
  linearCombination_single_index σ M R c s f

theorem weight_single_one_apply [DecidableEq σ] (s : σ) (f : σ →₀ R) :
    weight (Pi.single s 1) f = f s := by
  rw [weight_single_index, smul_eq_mul, mul_one]

theorem weight_single (s : σ) (r : R) :
    weight w (Finsupp.single s r) = r • w s :=
  Finsupp.linearCombination_single _ _ _

variable (R) in

class NonTorsionWeight (w : σ → M) : Prop where
  eq_zero_of_smul_eq_zero {r : R} {s : σ} (h : r • w s = 0) : r = 0

variable (R) in

-- DISSOLVED: nonTorsionWeight_of

variable (R) in

-- DISSOLVED: NonTorsionWeight.ne_zero

variable {w} in

-- DISSOLVED: weight_sub_single_add

end AddCommMonoid

section OrderedAddCommMonoid

-- DISSOLVED: le_weight

variable [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M] (w : σ → M)
  {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
  [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Module R M]

variable {w} in

-- DISSOLVED: le_weight_of_ne_zero

end OrderedAddCommMonoid

section CanonicallyOrderedAddCommMonoid

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [CanonicallyOrderedAdd M] (w : σ → M)

-- DISSOLVED: le_weight_of_ne_zero'

theorem weight_eq_zero_iff_eq_zero
    (w : σ → M) [NonTorsionWeight ℕ w] {f : σ →₀ ℕ} :
    weight w f = 0 ↔ f = 0 := by
  classical
  constructor
  · intro h
    ext s
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hs
    apply NonTorsionWeight.ne_zero ℕ w s
    rw [← nonpos_iff_eq_zero, ← h]
    exact le_weight_of_ne_zero' w hs
  · intro h
    rw [h, map_zero]

-- DISSOLVED: finite_of_nat_weight_le

end CanonicallyOrderedAddCommMonoid

variable {R : Type*} [AddCommMonoid R]

def degree : (σ →₀ R) →+ R where
  toFun := fun d => ∑ i ∈ d.support, d i
  map_zero' := by simp
  map_add' := fun _ _ => sum_add_index' (h := fun _ ↦ id) (congrFun rfl) fun _ _ ↦ congrFun rfl
