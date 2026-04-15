/-
Extracted from Algebra/Order/Group/Unbundled/Int.lean
Genuine: 18 | Conflates: 0 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Abs

/-!
# Facts about `ℤ` as an (unbundled) ordered group

See note [foundational algebra order theory].

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

open Function Nat

namespace Int

theorem natCast_strictMono : StrictMono (· : ℕ → ℤ) := fun _ _ ↦ Int.ofNat_lt.2

/-! ### Miscellaneous lemmas -/

theorem abs_eq_natAbs : ∀ a : ℤ, |a| = natAbs a
  | (n : ℕ) => abs_of_nonneg <| ofNat_zero_le _
  | -[_+1] => abs_of_nonpos <| le_of_lt <| negSucc_lt_zero _

@[simp, norm_cast] lemma natCast_natAbs (n : ℤ) : (n.natAbs : ℤ) = |n| := n.abs_eq_natAbs.symm

theorem natAbs_abs (a : ℤ) : natAbs |a| = natAbs a := by rw [abs_eq_natAbs]; rfl

theorem sign_mul_abs (a : ℤ) : sign a * |a| = a := by
  rw [abs_eq_natAbs, sign_mul_natAbs a]

lemma natAbs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by
  rw [← Int.natAbs_sq a, sq]
  norm_cast
  apply Nat.le_mul_self

alias natAbs_le_self_pow_two := natAbs_le_self_sq

lemma le_self_sq (b : ℤ) : b ≤ b ^ 2 := le_trans le_natAbs (natAbs_le_self_sq _)

alias le_self_pow_two := le_self_sq

@[norm_cast] lemma abs_natCast (n : ℕ) : |(n : ℤ)| = n := abs_of_nonneg (natCast_nonneg n)

theorem natAbs_sub_pos_iff {i j : ℤ} : 0 < natAbs (i - j) ↔ i ≠ j := by
  rw [natAbs_pos, ne_eq, sub_eq_zero]

-- DISSOLVED: natAbs_sub_ne_zero_iff

@[simp]
theorem abs_lt_one_iff {a : ℤ} : |a| < 1 ↔ a = 0 := by
  rw [← zero_add 1, lt_add_one_iff, abs_nonpos_iff]

theorem abs_le_one_iff {a : ℤ} : |a| ≤ 1 ↔ a = 0 ∨ a = 1 ∨ a = -1 := by
  rw [le_iff_lt_or_eq, abs_lt_one_iff]
  match a with
  | (n : ℕ) => simp [abs_eq_natAbs]
  | -[n+1] =>
      simp only [negSucc_ne_zero, abs_eq_natAbs, natAbs_negSucc, succ_eq_add_one,
        natCast_add, Nat.cast_ofNat_Int, add_left_eq_self, natCast_eq_zero, false_or, reduceNeg]
      rw [negSucc_eq']
      omega

-- DISSOLVED: one_le_abs

lemma eq_zero_of_abs_lt_dvd {m x : ℤ} (h1 : m ∣ x) (h2 : |x| < m) : x = 0 := by
  by_contra h
  have := Int.natAbs_le_of_dvd_ne_zero h1 h
  rw [Int.abs_eq_natAbs] at h2
  omega

lemma abs_sub_lt_of_lt_lt {m a b : ℕ} (ha : a < m) (hb : b < m) : |(b : ℤ) - a| < m := by
  rw [abs_lt]; omega

/-! #### `/`  -/

theorem ediv_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < |b|) : a / b = 0 :=
  match b, |b|, abs_eq_natAbs b, H2 with
  | (n : ℕ), _, rfl, H2 => ediv_eq_zero_of_lt H1 H2
  | -[n+1], _, rfl, H2 => neg_injective <| by rw [← Int.ediv_neg]; exact ediv_eq_zero_of_lt H1 H2

/-! #### mod -/

@[simp]
theorem emod_abs (a b : ℤ) : a % |b| = a % b :=
  abs_by_cases (fun i => a % i = a % b) rfl (emod_neg _ _)

-- DISSOLVED: emod_lt

/-! ### properties of `/` and `%` -/

theorem abs_ediv_le_abs : ∀ a b : ℤ, |a / b| ≤ |a| :=
  suffices ∀ (a : ℤ) (n : ℕ), |a / n| ≤ |a| from fun a b =>
    match b, eq_nat_or_neg b with
    | _, ⟨n, Or.inl rfl⟩ => this _ _
    | _, ⟨n, Or.inr rfl⟩ => by rw [Int.ediv_neg, abs_neg]; apply this
  fun a n => by
  rw [abs_eq_natAbs, abs_eq_natAbs];
  exact ofNat_le_ofNat_of_le
    (match a, n with
      | (m : ℕ), n => Nat.div_le_self _ _
      | -[m+1], 0 => Nat.zero_le _
      | -[m+1], n + 1 => Nat.succ_le_succ (Nat.div_le_self _ _))

-- DISSOLVED: abs_sign_of_nonzero

protected theorem sign_eq_ediv_abs (a : ℤ) : sign a = a / |a| :=
  if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left (mt abs_eq_zero.1 az) (sign_mul_abs _).symm).symm

end Int

section Group

variable {G : Type*} [Group G]

@[to_additive (attr := simp) abs_zsmul_eq_zero]
lemma zpow_abs_eq_one (a : G) (n : ℤ) : a ^ |n| = 1 ↔ a ^ n = 1 := by
  rw [← Int.natCast_natAbs, zpow_natCast, pow_natAbs_eq_one]

end Group
