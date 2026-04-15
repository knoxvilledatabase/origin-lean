/-
Extracted from Algebra/Polynomial/DenomsClearable.lean
Genuine: 6 | Conflates: 0 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Denominators of evaluation of polynomials at ratios

Let `i : R → K` be a homomorphism of semirings.  Assume that `K` is commutative.  If `a` and
`b` are elements of `R` such that `i b ∈ K` is invertible, then for any polynomial
`f ∈ R[X]` the "mathematical" expression `b ^ f.natDegree * f (a / b) ∈ K` is in
the image of the homomorphism `i`.
-/

open Polynomial Finset

open Polynomial

section DenomsClearable

variable {R K : Type*} [Semiring R] [CommSemiring K] {i : R →+* K}

variable {a b : R} {bi : K}

def DenomsClearable (a b : R) (N : ℕ) (f : R[X]) (i : R →+* K) : Prop :=
  ∃ (D : R) (bi : K), bi * i b = 1 ∧ i D = i b ^ N * eval (i a * bi) (f.map i)

theorem denomsClearable_zero (N : ℕ) (a : R) (bu : bi * i b = 1) : DenomsClearable a b N 0 i :=
  ⟨0, bi, bu, by
    simp only [eval_zero, RingHom.map_zero, mul_zero, Polynomial.map_zero]⟩

theorem denomsClearable_C_mul_X_pow {N : ℕ} (a : R) (bu : bi * i b = 1) {n : ℕ} (r : R)
    (nN : n ≤ N) : DenomsClearable a b N (C r * X ^ n) i := by
  refine ⟨r * a ^ n * b ^ (N - n), bi, bu, ?_⟩
  rw [C_mul_X_pow_eq_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, eval_mul, eval_pow, eval_C]
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow, eval_X, mul_comm]
  rw [← tsub_add_cancel_of_le nN]
  conv_lhs => rw [← mul_one (i a), ← bu]
  simp [mul_assoc, mul_comm, mul_left_comm, pow_add, mul_pow]

theorem DenomsClearable.add {N : ℕ} {f g : R[X]} :
    DenomsClearable a b N f i → DenomsClearable a b N g i → DenomsClearable a b N (f + g) i :=
  fun ⟨Df, bf, bfu, Hf⟩ ⟨Dg, bg, bgu, Hg⟩ =>
  ⟨Df + Dg, bf, bfu, by
    rw [RingHom.map_add, Polynomial.map_add, eval_add, mul_add, Hf, Hg]
    congr
    refine @inv_unique K _ (i b) bg bf ?_ ?_ <;> rwa [mul_comm]⟩

theorem denomsClearable_of_natDegree_le (N : ℕ) (a : R) (bu : bi * i b = 1) :
    ∀ f : R[X], f.natDegree ≤ N → DenomsClearable a b N f i :=
  induction_with_natDegree_le _ N (denomsClearable_zero N a bu)
    (fun _ r _ => denomsClearable_C_mul_X_pow a bu r) fun _ _ _ _ df dg => df.add dg

theorem denomsClearable_natDegree (i : R →+* K) (f : R[X]) (a : R) (bu : bi * i b = 1) :
    DenomsClearable a b f.natDegree f i :=
  denomsClearable_of_natDegree_le f.natDegree a bu f le_rfl

end DenomsClearable

open RingHom

-- DISSOLVED: one_le_pow_mul_abs_eval_div
