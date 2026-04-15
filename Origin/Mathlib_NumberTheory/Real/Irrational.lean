/-
Extracted from NumberTheory/Real/Irrational.lean
Genuine: 6 of 8 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Irrational real numbers

In this file we define a predicate `Irrational` on `ℝ`, prove that the `n`-th root of an integer
number is irrational if it is not integer, and that `√(q : ℚ)` is irrational if and only if
`¬IsSquare q ∧ 0 ≤ q`.

We also provide dot-style constructors like `Irrational.add_ratCast`, `Irrational.ratCast_sub` etc.

With the `Decidable` instances in this file, is possible to prove `Irrational √n` using `decide`,
when `n` is a numeric literal or cast;
but this only works if you `unseal Nat.sqrt.iter in` before the theorem where you use this proof.
-/

open Rat Real

def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)

-- DISSOLVED: irrational_iff_ne_rational

theorem Irrational.ne_rational {x : ℝ} (hx : Irrational x) (a b : ℤ) : x ≠ a / b := by
  rintro rfl; exact hx ⟨a / b, by simp⟩

theorem exists_rat_of_not_irrational {x : ℝ} (hx : ¬ Irrational x) : ∃ (q : ℚ), x = q := by
  grind [Irrational]

theorem Transcendental.irrational {r : ℝ} (tr : Transcendental ℚ r) : Irrational r := by
  rintro ⟨a, rfl⟩
  exact tr (isAlgebraic_algebraMap a)

/-!
### Irrationality of roots of integer and rational numbers
-/

theorem irrational_nrt_of_notint_nrt {x : ℝ} (n : ℕ) (m : ℤ) (hxr : x ^ n = m)
    (hv : ¬∃ y : ℤ, x = y) (hnpos : 0 < n) : Irrational x := by
  rintro ⟨⟨N, D, P, C⟩, rfl⟩
  rw [← cast_pow] at hxr
  have c1 : ((D : ℤ) : ℝ) ≠ 0 := by
    rw [Int.cast_ne_zero, Int.natCast_ne_zero]
    exact P
  have c2 : ((D : ℤ) : ℝ) ^ n ≠ 0 := pow_ne_zero _ c1
  rw [mk_eq_divInt, cast_pow, cast_divInt, div_pow, div_eq_iff_mul_eq c2, ← Int.cast_pow,
    ← Int.cast_pow, ← Int.cast_mul, Int.cast_inj] at hxr
  have hdivn : (D : ℤ) ^ n ∣ N ^ n := Dvd.intro_left m hxr
  rw [← Int.dvd_natAbs, ← Int.natCast_pow, Int.natCast_dvd_natCast, Int.natAbs_pow,
    Nat.pow_dvd_pow_iff hnpos.ne'] at hdivn
  obtain rfl : D = 1 := by rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  refine hv ⟨N, ?_⟩
  rw [mk_eq_divInt, Int.ofNat_one, divInt_one, cast_intCast]

-- DISSOLVED: irrational_nrt_of_n_not_dvd_multiplicity

theorem irrational_sqrt_of_multiplicity_odd (m : ℤ) (hm : 0 < m) (p : ℕ) [hp : Fact p.Prime]
    (Hpv : multiplicity (p : ℤ) m % 2 = 1) :
    Irrational (√m) :=
  @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (Ne.symm (ne_of_lt hm)) p hp
    (sq_sqrt (Int.cast_nonneg hm.le)) (by rw [Hpv]; exact one_ne_zero)
