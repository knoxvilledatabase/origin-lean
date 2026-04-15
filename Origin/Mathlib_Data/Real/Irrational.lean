/-
Extracted from Data/Real/Irrational.lean
Genuine: 65 of 118 | Dissolved: 28 | Infrastructure: 25
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Rat.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Irrational real numbers

In this file we define a predicate `Irrational` on `ℝ`, prove that the `n`-th root of an integer
number is irrational if it is not integer, and that `√(q : ℚ)` is irrational if and only if
`¬IsSquare q ∧ 0 ≤ q`.

We also provide dot-style constructors like `Irrational.add_rat`, `Irrational.rat_sub` etc.

With the `Decidable` instances in this file, is possible to prove `Irrational √n` using `decide`,
when `n` is a numeric literal or cast;
but this only works if you `unseal Nat.sqrt.iter in` before the theorem where you use this proof.
-/

open Rat Real multiplicity

def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)

theorem irrational_iff_ne_rational (x : ℝ) : Irrational x ↔ ∀ a b : ℤ, x ≠ a / b := by
  simp only [Irrational, Rat.forall, cast_mk, not_exists, Set.mem_range, cast_intCast, cast_div,
    eq_comm]

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
  rw [mk'_eq_divInt, cast_pow, cast_mk, div_pow, div_eq_iff_mul_eq c2, ← Int.cast_pow,
    ← Int.cast_pow, ← Int.cast_mul, Int.cast_inj] at hxr
  have hdivn : (D : ℤ) ^ n ∣ N ^ n := Dvd.intro_left m hxr
  rw [← Int.dvd_natAbs, ← Int.natCast_pow, Int.natCast_dvd_natCast, Int.natAbs_pow,
    Nat.pow_dvd_pow_iff hnpos.ne'] at hdivn
  obtain rfl : D = 1 := by rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  refine hv ⟨N, ?_⟩
  rw [mk'_eq_divInt, Int.ofNat_one, divInt_one, cast_intCast]

-- DISSOLVED: irrational_nrt_of_n_not_dvd_multiplicity

theorem irrational_sqrt_of_multiplicity_odd (m : ℤ) (hm : 0 < m) (p : ℕ) [hp : Fact p.Prime]
    (Hpv : multiplicity (p : ℤ) m % 2 = 1) :
    Irrational (√m) :=
  @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (Ne.symm (ne_of_lt hm)) p hp
    (sq_sqrt (Int.cast_nonneg.2 <| le_of_lt hm)) (by rw [Hpv]; exact one_ne_zero)

@[simp] theorem not_irrational_zero : ¬Irrational 0 := not_not_intro ⟨0, Rat.cast_zero⟩

@[simp] theorem not_irrational_one : ¬Irrational 1 := not_not_intro ⟨1, Rat.cast_one⟩

theorem irrational_sqrt_ratCast_iff_of_nonneg {q : ℚ} (hq : 0 ≤ q) :
    Irrational (√q) ↔ ¬IsSquare q := by
  refine Iff.not (?_ : Exists _ ↔ Exists _)
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Rat.cast_injective (α := ℝ) ?_⟩
    rw [Rat.cast_mul, hy, mul_self_sqrt (Rat.cast_nonneg.2 hq)]
  · rintro ⟨q', rfl⟩
    exact ⟨|q'|, mod_cast (sqrt_mul_self_eq_abs q').symm⟩

theorem irrational_sqrt_ratCast_iff {q : ℚ} :
    Irrational (√q) ↔ ¬IsSquare q ∧ 0 ≤ q := by
  obtain hq | hq := le_or_lt 0 q
  · simp_rw [irrational_sqrt_ratCast_iff_of_nonneg hq, and_iff_left hq]
  · rw [sqrt_eq_zero_of_nonpos (Rat.cast_nonpos.2 hq.le)]
    simp_rw [not_irrational_zero, false_iff, not_and, not_le, hq, implies_true]

theorem irrational_sqrt_intCast_iff_of_nonneg {z : ℤ} (hz : 0 ≤ z) :
    Irrational (√z) ↔ ¬IsSquare z := by
  rw [← Rat.isSquare_intCast_iff, ← irrational_sqrt_ratCast_iff_of_nonneg (mod_cast hz),
    Rat.cast_intCast]

theorem irrational_sqrt_intCast_iff {z : ℤ} :
    Irrational (√z) ↔ ¬IsSquare z ∧ 0 ≤ z := by
  rw [← Rat.cast_intCast, irrational_sqrt_ratCast_iff, Rat.isSquare_intCast_iff, Int.cast_nonneg]

theorem irrational_sqrt_natCast_iff {n : ℕ} : Irrational (√n) ↔ ¬IsSquare n := by
  rw [← Rat.isSquare_natCast_iff, ← irrational_sqrt_ratCast_iff_of_nonneg n.cast_nonneg,
    Rat.cast_natCast]

theorem irrational_sqrt_ofNat_iff {n : ℕ} [n.AtLeastTwo] :
    Irrational (√(no_index (OfNat.ofNat n))) ↔ ¬IsSquare (OfNat.ofNat n) :=
  irrational_sqrt_natCast_iff

theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (√p) :=
  irrational_sqrt_natCast_iff.mpr hp.not_square

theorem irrational_sqrt_two : Irrational (√2) := by
  simpa using Nat.prime_two.irrational_sqrt

theorem irrational_sqrt_rat_iff (q : ℚ) :
    Irrational (√q) ↔ Rat.sqrt q * Rat.sqrt q ≠ q ∧ 0 ≤ q := by
  rw [irrational_sqrt_ratCast_iff, ne_eq, ← Rat.exists_mul_self]
  simp only [eq_comm, IsSquare]

instance {n : ℕ} [n.AtLeastTwo] : Decidable (Irrational (√(no_index (OfNat.ofNat n)))) :=
  decidable_of_iff' _ irrational_sqrt_ofNat_iff

instance (n : ℕ) : Decidable (Irrational (√n)) :=
  decidable_of_iff' _ irrational_sqrt_natCast_iff

instance (z : ℤ) : Decidable (Irrational (√z)) :=
  decidable_of_iff' _ irrational_sqrt_intCast_iff

instance (q : ℚ) : Decidable (Irrational (√q)) :=
  decidable_of_iff' _ irrational_sqrt_ratCast_iff

/-!
### Dot-style operations on `Irrational`

#### Coercion of a rational/integer/natural number is not irrational
-/

namespace Irrational

variable {x : ℝ}

/-!
#### Irrational number is not equal to a rational/integer/natural number
-/

theorem ne_rat (h : Irrational x) (q : ℚ) : x ≠ q := fun hq => h ⟨q, hq.symm⟩

theorem ne_int (h : Irrational x) (m : ℤ) : x ≠ m := by
  rw [← Rat.cast_intCast]
  exact h.ne_rat _

theorem ne_nat (h : Irrational x) (m : ℕ) : x ≠ m :=
  h.ne_int m

-- DISSOLVED: ne_zero

-- DISSOLVED: ne_one

@[simp] theorem ne_ofNat (h : Irrational x) (n : ℕ) [n.AtLeastTwo] : x ≠ no_index (OfNat.ofNat n) :=
  h.ne_nat n

end Irrational

@[simp]
theorem Rat.not_irrational (q : ℚ) : ¬Irrational q := fun h => h ⟨q, rfl⟩

@[simp]
theorem Int.not_irrational (m : ℤ) : ¬Irrational m := fun h => h.ne_int m rfl

@[simp]
theorem Nat.not_irrational (m : ℕ) : ¬Irrational m := fun h => h.ne_nat m rfl

@[simp] theorem not_irrational_ofNat (n : ℕ) [n.AtLeastTwo] :
    ¬Irrational (no_index (OfNat.ofNat n)) :=
  n.not_irrational

namespace Irrational

variable (q : ℚ) {x y : ℝ}

/-!
#### Addition of rational/integer/natural numbers
-/

theorem add_cases : Irrational (x + y) → Irrational x ∨ Irrational y := by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx + ry, cast_add rx ry⟩

theorem of_rat_add (h : Irrational (q + x)) : Irrational x :=
  h.add_cases.resolve_left q.not_irrational

theorem rat_add (h : Irrational x) : Irrational (q + x) :=
  of_rat_add (-q) <| by rwa [cast_neg, neg_add_cancel_left]

theorem of_add_rat : Irrational (x + q) → Irrational x :=
  add_comm (↑q) x ▸ of_rat_add q

theorem add_rat (h : Irrational x) : Irrational (x + q) :=
  add_comm (↑q) x ▸ h.rat_add q

theorem of_int_add (m : ℤ) (h : Irrational (m + x)) : Irrational x := by
  rw [← cast_intCast] at h
  exact h.of_rat_add m

theorem of_add_int (m : ℤ) (h : Irrational (x + m)) : Irrational x :=
  of_int_add m <| add_comm x m ▸ h

theorem int_add (h : Irrational x) (m : ℤ) : Irrational (m + x) := by
  rw [← cast_intCast]
  exact h.rat_add m

theorem add_int (h : Irrational x) (m : ℤ) : Irrational (x + m) :=
  add_comm (↑m) x ▸ h.int_add m

theorem of_nat_add (m : ℕ) (h : Irrational (m + x)) : Irrational x :=
  h.of_int_add m

theorem of_add_nat (m : ℕ) (h : Irrational (x + m)) : Irrational x :=
  h.of_add_int m

theorem nat_add (h : Irrational x) (m : ℕ) : Irrational (m + x) :=
  h.int_add m

theorem add_nat (h : Irrational x) (m : ℕ) : Irrational (x + m) :=
  h.add_int m

/-!
#### Negation
-/

theorem of_neg (h : Irrational (-x)) : Irrational x := fun ⟨q, hx⟩ => h ⟨-q, by rw [cast_neg, hx]⟩

protected theorem neg (h : Irrational x) : Irrational (-x) :=
  of_neg <| by rwa [neg_neg]

/-!
#### Subtraction of rational/integer/natural numbers
-/

theorem sub_rat (h : Irrational x) : Irrational (x - q) := by
  simpa only [sub_eq_add_neg, cast_neg] using h.add_rat (-q)

theorem rat_sub (h : Irrational x) : Irrational (q - x) := by
  simpa only [sub_eq_add_neg] using h.neg.rat_add q

theorem of_sub_rat (h : Irrational (x - q)) : Irrational x :=
  of_add_rat (-q) <| by simpa only [cast_neg, sub_eq_add_neg] using h

theorem of_rat_sub (h : Irrational (q - x)) : Irrational x :=
  of_neg (of_rat_add q (by simpa only [sub_eq_add_neg] using h))

theorem sub_int (h : Irrational x) (m : ℤ) : Irrational (x - m) := by
  simpa only [Rat.cast_intCast] using h.sub_rat m

theorem int_sub (h : Irrational x) (m : ℤ) : Irrational (m - x) := by
  simpa only [Rat.cast_intCast] using h.rat_sub m

theorem of_sub_int (m : ℤ) (h : Irrational (x - m)) : Irrational x :=
  of_sub_rat m <| by rwa [Rat.cast_intCast]

theorem of_int_sub (m : ℤ) (h : Irrational (m - x)) : Irrational x :=
  of_rat_sub m <| by rwa [Rat.cast_intCast]

theorem sub_nat (h : Irrational x) (m : ℕ) : Irrational (x - m) :=
  h.sub_int m

theorem nat_sub (h : Irrational x) (m : ℕ) : Irrational (m - x) :=
  h.int_sub m

theorem of_sub_nat (m : ℕ) (h : Irrational (x - m)) : Irrational x :=
  h.of_sub_int m

theorem of_nat_sub (m : ℕ) (h : Irrational (m - x)) : Irrational x :=
  h.of_int_sub m

/-!
#### Multiplication by rational numbers
-/

theorem mul_cases : Irrational (x * y) → Irrational x ∨ Irrational y := by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx * ry, cast_mul rx ry⟩

theorem of_mul_rat (h : Irrational (x * q)) : Irrational x :=
  h.mul_cases.resolve_right q.not_irrational

-- DISSOLVED: mul_rat

theorem of_rat_mul : Irrational (q * x) → Irrational x :=
  mul_comm x q ▸ of_mul_rat q

-- DISSOLVED: rat_mul

theorem of_mul_int (m : ℤ) (h : Irrational (x * m)) : Irrational x :=
  of_mul_rat m <| by rwa [cast_intCast]

theorem of_int_mul (m : ℤ) (h : Irrational (m * x)) : Irrational x :=
  of_rat_mul m <| by rwa [cast_intCast]

-- DISSOLVED: mul_int

-- DISSOLVED: int_mul

theorem of_mul_nat (m : ℕ) (h : Irrational (x * m)) : Irrational x :=
  h.of_mul_int m

theorem of_nat_mul (m : ℕ) (h : Irrational (m * x)) : Irrational x :=
  h.of_int_mul m

-- DISSOLVED: mul_nat

-- DISSOLVED: nat_mul

/-!
#### Inverse
-/

theorem of_inv (h : Irrational x⁻¹) : Irrational x := fun ⟨q, hq⟩ => h <| hq ▸ ⟨q⁻¹, q.cast_inv⟩

protected theorem inv (h : Irrational x) : Irrational x⁻¹ :=
  of_inv <| by rwa [inv_inv]

/-!
#### Division
-/

theorem div_cases (h : Irrational (x / y)) : Irrational x ∨ Irrational y :=
  h.mul_cases.imp id of_inv

theorem of_rat_div (h : Irrational (q / x)) : Irrational x :=
  (h.of_rat_mul q).of_inv

theorem of_div_rat (h : Irrational (x / q)) : Irrational x :=
  h.div_cases.resolve_right q.not_irrational

-- DISSOLVED: rat_div

-- DISSOLVED: div_rat

theorem of_int_div (m : ℤ) (h : Irrational (m / x)) : Irrational x :=
  h.div_cases.resolve_left m.not_irrational

theorem of_div_int (m : ℤ) (h : Irrational (x / m)) : Irrational x :=
  h.div_cases.resolve_right m.not_irrational

-- DISSOLVED: int_div

-- DISSOLVED: div_int

theorem of_nat_div (m : ℕ) (h : Irrational (m / x)) : Irrational x :=
  h.of_int_div m

theorem of_div_nat (m : ℕ) (h : Irrational (x / m)) : Irrational x :=
  h.of_div_int m

-- DISSOLVED: nat_div

-- DISSOLVED: div_nat

theorem of_one_div (h : Irrational (1 / x)) : Irrational x :=
  of_rat_div 1 <| by rwa [cast_one]

/-!
#### Natural and integer power
-/

theorem of_mul_self (h : Irrational (x * x)) : Irrational x :=
  h.mul_cases.elim id id

theorem of_pow : ∀ n : ℕ, Irrational (x ^ n) → Irrational x
  | 0 => fun h => by
    rw [pow_zero] at h
    exact (h ⟨1, cast_one⟩).elim
  | n + 1 => fun h => by
    rw [pow_succ] at h
    exact h.mul_cases.elim (of_pow n) id

open Int in

theorem of_zpow : ∀ m : ℤ, Irrational (x ^ m) → Irrational x
  | (n : ℕ) => fun h => by
    rw [zpow_natCast] at h
    exact h.of_pow _
  | -[n+1] => fun h => by
    rw [zpow_negSucc] at h
    exact h.of_inv.of_pow _

end Irrational

section Polynomial

open Polynomial

variable (x : ℝ) (p : ℤ[X])

-- DISSOLVED: one_lt_natDegree_of_irrational_root

end Polynomial

section

variable {q : ℚ} {m : ℤ} {n : ℕ} {x : ℝ}

open Irrational

/-!
### Simplification lemmas about operations
-/

@[simp]
theorem irrational_rat_add_iff : Irrational (q + x) ↔ Irrational x :=
  ⟨of_rat_add q, rat_add q⟩

@[simp]
theorem irrational_int_add_iff : Irrational (m + x) ↔ Irrational x :=
  ⟨of_int_add m, fun h => h.int_add m⟩

@[simp]
theorem irrational_nat_add_iff : Irrational (n + x) ↔ Irrational x :=
  ⟨of_nat_add n, fun h => h.nat_add n⟩

@[simp]
theorem irrational_add_rat_iff : Irrational (x + q) ↔ Irrational x :=
  ⟨of_add_rat q, add_rat q⟩

@[simp]
theorem irrational_add_int_iff : Irrational (x + m) ↔ Irrational x :=
  ⟨of_add_int m, fun h => h.add_int m⟩

@[simp]
theorem irrational_add_nat_iff : Irrational (x + n) ↔ Irrational x :=
  ⟨of_add_nat n, fun h => h.add_nat n⟩

@[simp]
theorem irrational_rat_sub_iff : Irrational (q - x) ↔ Irrational x :=
  ⟨of_rat_sub q, rat_sub q⟩

@[simp]
theorem irrational_int_sub_iff : Irrational (m - x) ↔ Irrational x :=
  ⟨of_int_sub m, fun h => h.int_sub m⟩

@[simp]
theorem irrational_nat_sub_iff : Irrational (n - x) ↔ Irrational x :=
  ⟨of_nat_sub n, fun h => h.nat_sub n⟩

@[simp]
theorem irrational_sub_rat_iff : Irrational (x - q) ↔ Irrational x :=
  ⟨of_sub_rat q, sub_rat q⟩

@[simp]
theorem irrational_sub_int_iff : Irrational (x - m) ↔ Irrational x :=
  ⟨of_sub_int m, fun h => h.sub_int m⟩

@[simp]
theorem irrational_sub_nat_iff : Irrational (x - n) ↔ Irrational x :=
  ⟨of_sub_nat n, fun h => h.sub_nat n⟩

@[simp]
theorem irrational_neg_iff : Irrational (-x) ↔ Irrational x :=
  ⟨of_neg, Irrational.neg⟩

@[simp]
theorem irrational_inv_iff : Irrational x⁻¹ ↔ Irrational x :=
  ⟨of_inv, Irrational.inv⟩

-- DISSOLVED: irrational_rat_mul_iff

-- DISSOLVED: irrational_mul_rat_iff

-- DISSOLVED: irrational_int_mul_iff

-- DISSOLVED: irrational_mul_int_iff

-- DISSOLVED: irrational_nat_mul_iff

-- DISSOLVED: irrational_mul_nat_iff

-- DISSOLVED: irrational_rat_div_iff

-- DISSOLVED: irrational_div_rat_iff

-- DISSOLVED: irrational_int_div_iff

-- DISSOLVED: irrational_div_int_iff

-- DISSOLVED: irrational_nat_div_iff

-- DISSOLVED: irrational_div_nat_iff

theorem exists_irrational_btwn {x y : ℝ} (h : x < y) : ∃ r, Irrational r ∧ x < r ∧ r < y :=
  let ⟨q, ⟨hq1, hq2⟩⟩ := exists_rat_btwn ((sub_lt_sub_iff_right (√2)).mpr h)
  ⟨q + √2, irrational_sqrt_two.rat_add _, sub_lt_iff_lt_add.mp hq1, lt_sub_iff_add_lt.mp hq2⟩

end
