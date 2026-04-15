/-
Extracted from RingTheory/MvPolynomial/WeightedHomogeneous.lean
Genuine: 8 of 9 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Weighted homogeneous polynomials

It is possible to assign weights (in a commutative additive monoid `M`) to the variables of a
multivariate polynomial ring, so that monomials of the ring then have a weighted degree with
respect to the weights of the variables. The weights are represented by a function `w : σ → M`,
where `σ` are the indeterminates.

A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m : M` if all monomials
occurring in `φ` have the same weighted degree `m`.

## Main definitions/lemmas

* `weightedTotalDegree' w φ` : the weighted total degree of a multivariate polynomial with respect
  to the weights `w`, taking values in `WithBot M`.

* `weightedTotalDegree w φ` : When `M` has a `⊥` element, we can define the weighted total degree
  of a multivariate polynomial as a function taking values in `M`.

* `IsWeightedHomogeneous w φ m`: a predicate that asserts that `φ` is weighted homogeneous
  of weighted degree `m` with respect to the weights `w`.

* `weightedHomogeneousSubmodule R w m`: the submodule of homogeneous polynomials
  of weighted degree `m`.

* `weightedHomogeneousComponent w m`: the additive morphism that projects polynomials
  onto their summand that is weighted homogeneous of degree `n` with respect to `w`.

* `sum_weightedHomogeneousComponent`: every polynomial is the sum of its weighted homogeneous
  components.
-/

noncomputable section

open Set Function Finset Finsupp AddMonoidAlgebra

variable {R M : Type*} [CommSemiring R]

namespace MvPolynomial

variable {σ : Type*}

section AddCommMonoid

variable [AddCommMonoid M]

/-! ### `weight` -/

section SemilatticeSup

variable [SemilatticeSup M]

def weightedTotalDegree' (w : σ → M) (p : MvPolynomial σ R) : WithBot M :=
  p.support.sup fun s => weight w s

theorem weightedTotalDegree'_eq_bot_iff (w : σ → M) (p : MvPolynomial σ R) :
    weightedTotalDegree' w p = ⊥ ↔ p = 0 := by
  simp only [weightedTotalDegree', Finset.sup_eq_bot_iff, mem_support_iff, WithBot.coe_ne_bot,
    MvPolynomial.eq_zero_iff]
  exact forall_congr' fun _ => Classical.not_not

theorem weightedTotalDegree'_zero (w : σ → M) :
    weightedTotalDegree' w (0 : MvPolynomial σ R) = ⊥ := by
  simp only [weightedTotalDegree', support_zero, Finset.sup_empty]

section OrderBot

variable [OrderBot M]

def weightedTotalDegree (w : σ → M) (p : MvPolynomial σ R) : M :=
  p.support.sup fun s => weight w s

-- DISSOLVED: weightedTotalDegree_coe

theorem weightedTotalDegree_zero (w : σ → M) :
    weightedTotalDegree w (0 : MvPolynomial σ R) = ⊥ := by
  simp only [weightedTotalDegree, support_zero, Finset.sup_empty]

theorem le_weightedTotalDegree (w : σ → M) {φ : MvPolynomial σ R} {d : σ →₀ ℕ}
    (hd : d ∈ φ.support) : weight w d ≤ φ.weightedTotalDegree w :=
  le_sup hd

end OrderBot

end SemilatticeSup

def IsWeightedHomogeneous (w : σ → M) (φ : MvPolynomial σ R) (m : M) : Prop :=
  ∀ ⦃d⦄, coeff d φ ≠ 0 → weight w d = m

variable (R)

def weightedHomogeneousSubmodule (w : σ → M) (m : M) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsWeightedHomogeneous w m }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    exact ha (right_ne_zero_of_mul hc)
  zero_mem' _ hd := False.elim (hd <| coeff_zero _)
  add_mem' {a} {b} ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by
      contrapose! hc
      simp only [hc, add_zero]
    · exact ha h
    · exact hb h
