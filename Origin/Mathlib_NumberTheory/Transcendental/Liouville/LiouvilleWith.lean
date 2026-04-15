/-
Extracted from NumberTheory/Transcendental/Liouville/LiouvilleWith.lean
Genuine: 6 of 18 | Dissolved: 12 | Infrastructure: 0
-/
import Origin.Core

/-!
# Liouville numbers with a given exponent

We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`. A number is a Liouville number in the sense of
`Liouville` if it is `LiouvilleWith` any real exponent, see `forall_liouvilleWith_iff`.

* If `p ≤ 1`, then this condition is trivial.

* If `1 < p ≤ 2`, then this condition is equivalent to `Irrational x`. The forward implication
  does not require `p ≤ 2` and is formalized as `LiouvilleWith.irrational`; the other implication
  follows from approximations by continued fractions and is not formalized yet.

* If `p > 2`, then this is a non-trivial condition on irrational numbers. In particular,
  [Thue–Siegel–Roth theorem](https://en.wikipedia.org/wiki/Roth's_theorem) states that such numbers
  must be transcendental.

In this file we define the predicate `LiouvilleWith` and prove some basic facts about this
predicate.

## Tags

Liouville number, irrational, irrationality exponent
-/

open Filter Metric Real Set

open scoped Filter Topology

def LiouvilleWith (p x : ℝ) : Prop :=
  ∃ C, ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p

theorem liouvilleWith_one (x : ℝ) : LiouvilleWith 1 x := by
  use 2
  refine ((eventually_gt_atTop 0).mono fun n hn => ?_).frequently
  have hn' : (0 : ℝ) < n := by simpa
  have : x < ↑(⌊x * ↑n⌋ + 1) / ↑n := by
    rw [lt_div_iff₀ hn', Int.cast_add, Int.cast_one]
    exact Int.lt_floor_add_one _
  refine ⟨⌊x * n⌋ + 1, this.ne, ?_⟩
  rw [abs_sub_comm, abs_of_pos (sub_pos.2 this), rpow_one, sub_lt_iff_lt_add',
    add_div_eq_mul_add_div _ _ hn'.ne']
  gcongr
  calc _ ≤ x * n + 1 := by push_cast; gcongr; apply Int.floor_le
    _ < x * n + 2 := by linarith

namespace LiouvilleWith

variable {p q x : ℝ} {r : ℚ} {m : ℤ} {n : ℕ}

theorem exists_pos (h : LiouvilleWith p x) :
    ∃ (C : ℝ) (_h₀ : 0 < C),
      ∃ᶠ n : ℕ in atTop, 1 ≤ n ∧ ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p := by
  rcases h with ⟨C, hC⟩
  refine ⟨max C 1, zero_lt_one.trans_le <| le_max_right _ _, ?_⟩
  refine ((eventually_ge_atTop 1).and_frequently hC).mono ?_
  rintro n ⟨hle, m, hne, hlt⟩
  refine ⟨hle, m, hne, hlt.trans_le ?_⟩
  gcongr
  apply le_max_left

theorem mono (h : LiouvilleWith p x) (hle : q ≤ p) : LiouvilleWith q x := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  refine ⟨C, hC.mono ?_⟩; rintro n ⟨hn, m, hne, hlt⟩
  refine ⟨m, hne, hlt.trans_le <| ?_⟩
  gcongr
  exact_mod_cast hn

theorem frequently_lt_rpow_neg (h : LiouvilleWith p x) (hlt : q < p) :
    ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < n ^ (-q) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  have : ∀ᶠ n : ℕ in atTop, C < n ^ (p - q) := by
    simpa only [(· ∘ ·), neg_sub, one_div] using
      ((tendsto_rpow_atTop (sub_pos.2 hlt)).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop C)
  refine (this.and_frequently hC).mono ?_
  rintro n ⟨hnC, hn, m, hne, hlt⟩
  replace hn : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨m, hne, hlt.trans <| (div_lt_iff₀ <| rpow_pos_of_pos hn _).2 ?_⟩
  rwa [mul_comm, ← rpow_add hn, ← sub_eq_add_neg]

-- DISSOLVED: mul_rat

-- DISSOLVED: mul_rat_iff

-- DISSOLVED: rat_mul_iff

-- DISSOLVED: rat_mul

-- DISSOLVED: mul_int_iff

-- DISSOLVED: mul_int

-- DISSOLVED: int_mul_iff

-- DISSOLVED: int_mul

-- DISSOLVED: mul_nat_iff

-- DISSOLVED: mul_nat

-- DISSOLVED: nat_mul_iff

-- DISSOLVED: nat_mul

theorem add_rat (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (x + r) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * C, (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨hn, m, hne, hlt⟩
  have : (↑(r.den * m + r.num * n : ℤ) / ↑(r.den • id n) : ℝ) = m / n + r := by
    rw [smul_eq_mul, id]
    nth_rewrite 4 [← Rat.num_div_den r]
    push_cast
    rw [add_div, mul_div_mul_left _ _ (by positivity), mul_div_mul_right _ _ (by positivity)]
  refine ⟨r.den * m + r.num * n, ?_⟩; rw [this, add_sub_add_right_eq_sub]
  refine ⟨by simpa, hlt.trans_le (le_of_eq ?_)⟩
  have : (r.den ^ p : ℝ) ≠ 0 := by positivity
  simp [mul_rpow, mul_div_mul_left, this]
