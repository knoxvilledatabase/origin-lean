/-
Extracted from RingTheory/MvPolynomial/Ideal.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.MonoidAlgebra.Ideal
import Mathlib.Algebra.MvPolynomial.Division

noncomputable section

/-!
# Lemmas about ideals of `MvPolynomial`

Notably this contains results about monomial ideals.

## Main results

* `MvPolynomial.mem_ideal_span_monomial_image`
* `MvPolynomial.mem_ideal_span_X_image`
-/

variable {σ R : Type*}

namespace MvPolynomial

variable [CommSemiring R]

theorem mem_ideal_span_monomial_image {x : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    x ∈ Ideal.span ((fun s => monomial s (1 : R)) '' s) ↔ ∀ xi ∈ x.support, ∃ si ∈ s, si ≤ xi := by
  refine AddMonoidAlgebra.mem_ideal_span_of'_image.trans ?_
  simp_rw [le_iff_exists_add, add_comm]
  rfl

theorem mem_ideal_span_monomial_image_iff_dvd {x : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    x ∈ Ideal.span ((fun s => monomial s (1 : R)) '' s) ↔
      ∀ xi ∈ x.support, ∃ si ∈ s, monomial si 1 ∣ monomial xi (x.coeff xi) := by
  refine mem_ideal_span_monomial_image.trans (forall₂_congr fun xi hxi => ?_)
  simp_rw [monomial_dvd_monomial, one_dvd, and_true, mem_support_iff.mp hxi, false_or]

theorem mem_ideal_span_X_image {x : MvPolynomial σ R} {s : Set σ} :
    x ∈ Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial σ R)) ↔
      ∀ m ∈ x.support, ∃ i ∈ s, (m : σ →₀ ℕ) i ≠ 0 := by
  have := @mem_ideal_span_monomial_image σ R _ x ((fun i => Finsupp.single i 1) '' s)
  rw [Set.image_image] at this
  refine this.trans ?_
  simp [Nat.one_le_iff_ne_zero]

end MvPolynomial
