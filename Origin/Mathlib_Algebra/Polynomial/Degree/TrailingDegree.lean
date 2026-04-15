/-
Extracted from Algebra/Polynomial/Degree/TrailingDegree.lean
Genuine: 46 | Conflates: 0 | Dissolved: 28 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Lattice

/-!
# Trailing degree of univariate polynomials

## Main definitions

* `trailingDegree p`: the multiplicity of `X` in the polynomial `p`
* `natTrailingDegree`: a variant of `trailingDegree` that takes values in the natural numbers
* `trailingCoeff`: the coefficient at index `natTrailingDegree p`

Converts most results about `degree`, `natDegree` and `leadingCoeff` to results about the bottom
end of a polynomial
-/

noncomputable section

open Function Polynomial Finsupp Finset

open scoped Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

def trailingDegree (p : R[X]) : ℕ∞ :=
  p.support.min

theorem trailingDegree_lt_wf : WellFounded fun p q : R[X] => trailingDegree p < trailingDegree q :=
  InvImage.wf trailingDegree wellFounded_lt

def natTrailingDegree (p : R[X]) : ℕ :=
  ENat.toNat (trailingDegree p)

def trailingCoeff (p : R[X]) : R :=
  coeff p (natTrailingDegree p)

def TrailingMonic (p : R[X]) :=
  trailingCoeff p = (1 : R)

theorem TrailingMonic.def : TrailingMonic p ↔ trailingCoeff p = 1 :=
  Iff.rfl

instance TrailingMonic.decidable [DecidableEq R] : Decidable (TrailingMonic p) :=
  inferInstanceAs <| Decidable (trailingCoeff p = (1 : R))

@[simp]
theorem TrailingMonic.trailingCoeff {p : R[X]} (hp : p.TrailingMonic) : trailingCoeff p = 1 :=
  hp

@[simp]
theorem trailingDegree_zero : trailingDegree (0 : R[X]) = ⊤ :=
  rfl

@[simp]
theorem trailingCoeff_zero : trailingCoeff (0 : R[X]) = 0 :=
  rfl

@[simp]
theorem natTrailingDegree_zero : natTrailingDegree (0 : R[X]) = 0 :=
  rfl

@[simp]
theorem trailingDegree_eq_top : trailingDegree p = ⊤ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.min_eq_top.1 h), fun h => by simp [h]⟩

-- DISSOLVED: trailingDegree_eq_natTrailingDegree

-- DISSOLVED: trailingDegree_eq_iff_natTrailingDegree_eq

-- DISSOLVED: trailingDegree_eq_iff_natTrailingDegree_eq_of_pos

theorem natTrailingDegree_eq_of_trailingDegree_eq_some {p : R[X]} {n : ℕ}
    (h : trailingDegree p = n) : natTrailingDegree p = n := by
  simp [natTrailingDegree, h]

@[simp]
theorem natTrailingDegree_le_trailingDegree : ↑(natTrailingDegree p) ≤ trailingDegree p :=
  ENat.coe_toNat_le_self _

theorem natTrailingDegree_eq_of_trailingDegree_eq [Semiring S] {q : S[X]}
    (h : trailingDegree p = trailingDegree q) : natTrailingDegree p = natTrailingDegree q := by
  unfold natTrailingDegree
  rw [h]

-- DISSOLVED: trailingDegree_le_of_ne_zero

-- DISSOLVED: natTrailingDegree_le_of_ne_zero

@[simp] lemma coeff_natTrailingDegree_eq_zero : coeff p p.natTrailingDegree = 0 ↔ p = 0 := by
  constructor
  · rintro h
    by_contra hp
    obtain ⟨n, hpn, hn⟩ := by simpa using min_mem_image_coe <| support_nonempty.2 hp
    obtain rfl := (trailingDegree_eq_iff_natTrailingDegree_eq hp).1 hn.symm
    exact hpn h
  · rintro rfl
    simp

-- DISSOLVED: coeff_natTrailingDegree_ne_zero

-- DISSOLVED: trailingDegree_eq_zero

-- DISSOLVED: natTrailingDegree_eq_zero

-- DISSOLVED: natTrailingDegree_ne_zero

-- DISSOLVED: trailingDegree_ne_zero

-- DISSOLVED: trailingDegree_le_trailingDegree

theorem trailingDegree_ne_of_natTrailingDegree_ne {n : ℕ} :
    p.natTrailingDegree ≠ n → trailingDegree p ≠ n :=
  mt fun h => by rw [natTrailingDegree, h, ENat.toNat_coe]

-- DISSOLVED: natTrailingDegree_le_of_trailingDegree_le

-- DISSOLVED: natTrailingDegree_le_natTrailingDegree

-- DISSOLVED: trailingDegree_monomial

-- DISSOLVED: natTrailingDegree_monomial

theorem natTrailingDegree_monomial_le : natTrailingDegree (monomial n a) ≤ n :=
  letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (natTrailingDegree_monomial ha).le

theorem le_trailingDegree_monomial : ↑n ≤ trailingDegree (monomial n a) :=
  letI := Classical.decEq R
  if ha : a = 0 then by simp [ha] else (trailingDegree_monomial ha).ge

-- DISSOLVED: trailingDegree_C

theorem le_trailingDegree_C : (0 : ℕ∞) ≤ trailingDegree (C a) :=
  le_trailingDegree_monomial

theorem trailingDegree_one_le : (0 : ℕ∞) ≤ trailingDegree (1 : R[X]) := by
  rw [← C_1]
  exact le_trailingDegree_C

@[simp]
theorem natTrailingDegree_C (a : R) : natTrailingDegree (C a) = 0 :=
  nonpos_iff_eq_zero.1 natTrailingDegree_monomial_le

@[simp]
theorem natTrailingDegree_one : natTrailingDegree (1 : R[X]) = 0 :=
  natTrailingDegree_C 1

@[simp]
theorem natTrailingDegree_natCast (n : ℕ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_natCast, natTrailingDegree_C]

alias natTrailingDegree_nat_cast := natTrailingDegree_natCast

-- DISSOLVED: trailingDegree_C_mul_X_pow

theorem le_trailingDegree_C_mul_X_pow (n : ℕ) (a : R) :
    (n : ℕ∞) ≤ trailingDegree (C a * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial]
  exact le_trailingDegree_monomial

theorem coeff_eq_zero_of_lt_trailingDegree (h : (n : ℕ∞) < trailingDegree p) : coeff p n = 0 :=
  Classical.not_not.1 (mt trailingDegree_le_of_ne_zero (not_le_of_gt h))

theorem coeff_eq_zero_of_lt_natTrailingDegree {p : R[X]} {n : ℕ} (h : n < p.natTrailingDegree) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_lt_trailingDegree
  by_cases hp : p = 0
  · rw [hp, trailingDegree_zero]
    exact WithTop.coe_lt_top n
  · rw [trailingDegree_eq_natTrailingDegree hp]
    exact WithTop.coe_lt_coe.2 h

@[simp]
theorem coeff_natTrailingDegree_pred_eq_zero {p : R[X]} {hp : (0 : ℕ∞) < natTrailingDegree p} :
    p.coeff (p.natTrailingDegree - 1) = 0 :=
  coeff_eq_zero_of_lt_natTrailingDegree <|
    Nat.sub_lt (WithTop.coe_pos.mp hp) Nat.one_pos

theorem le_trailingDegree_X_pow (n : ℕ) : (n : ℕ∞) ≤ trailingDegree (X ^ n : R[X]) := by
  simpa only [C_1, one_mul] using le_trailingDegree_C_mul_X_pow n (1 : R)

theorem le_trailingDegree_X : (1 : ℕ∞) ≤ trailingDegree (X : R[X]) :=
  le_trailingDegree_monomial

theorem natTrailingDegree_X_le : (X : R[X]).natTrailingDegree ≤ 1 :=
  natTrailingDegree_monomial_le

@[simp]
theorem trailingCoeff_eq_zero : trailingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    _root_.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h)
        (mem_of_min (trailingDegree_eq_natTrailingDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

-- DISSOLVED: trailingCoeff_nonzero_iff_nonzero

-- DISSOLVED: natTrailingDegree_mem_support_of_nonzero

theorem natTrailingDegree_le_of_mem_supp (a : ℕ) : a ∈ p.support → natTrailingDegree p ≤ a :=
  natTrailingDegree_le_of_ne_zero ∘ mem_support_iff.mp

-- DISSOLVED: natTrailingDegree_eq_support_min'

-- DISSOLVED: le_natTrailingDegree

theorem natTrailingDegree_le_natDegree (p : R[X]) : p.natTrailingDegree ≤ p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero, natTrailingDegree_zero]
  · exact le_natDegree_of_ne_zero (mt trailingCoeff_eq_zero.mp hp)

-- DISSOLVED: natTrailingDegree_mul_X_pow

theorem le_trailingDegree_mul : p.trailingDegree + q.trailingDegree ≤ (p * q).trailingDegree := by
  refine Finset.le_min fun n hn => ?_
  rw [mem_support_iff, coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  refine
    (add_le_add (min_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (min_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans
      (le_of_eq ?_)
  rwa [← WithTop.coe_add, WithTop.coe_eq_coe, ← mem_antidiagonal]

-- DISSOLVED: le_natTrailingDegree_mul

theorem coeff_mul_natTrailingDegree_add_natTrailingDegree : (p * q).coeff
    (p.natTrailingDegree + q.natTrailingDegree) = p.trailingCoeff * q.trailingCoeff := by
  rw [coeff_mul]
  refine
    Finset.sum_eq_single (p.natTrailingDegree, q.natTrailingDegree) ?_ fun h =>
      (h (mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  rw [mem_antidiagonal] at h₁
  by_cases hi : i < p.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
  by_cases hj : j < q.natTrailingDegree
  · rw [coeff_eq_zero_of_lt_natTrailingDegree hj, mul_zero]
  rw [not_lt] at hi hj
  refine (h₂ (Prod.ext_iff.mpr ?_).symm).elim
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm

-- DISSOLVED: trailingDegree_mul'

-- DISSOLVED: natTrailingDegree_mul'

-- DISSOLVED: natTrailingDegree_mul

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem trailingDegree_one : trailingDegree (1 : R[X]) = (0 : ℕ∞) :=
  trailingDegree_C one_ne_zero

@[simp]
theorem trailingDegree_X : trailingDegree (X : R[X]) = 1 :=
  trailingDegree_monomial one_ne_zero

@[simp]
theorem natTrailingDegree_X : (X : R[X]).natTrailingDegree = 1 :=
  natTrailingDegree_monomial one_ne_zero

@[simp]
lemma trailingDegree_X_pow (n : ℕ) :
    (X ^ n : R[X]).trailingDegree = n := by
  rw [X_pow_eq_monomial, trailingDegree_monomial one_ne_zero]

@[simp]
lemma natTrailingDegree_X_pow (n : ℕ) :
    (X ^ n : R[X]).natTrailingDegree = n := by
  rw [X_pow_eq_monomial, natTrailingDegree_monomial one_ne_zero]

end NonzeroSemiring

section Ring

variable [Ring R]

@[simp]
theorem trailingDegree_neg (p : R[X]) : trailingDegree (-p) = trailingDegree p := by
  unfold trailingDegree
  rw [support_neg]

@[simp]
theorem natTrailingDegree_neg (p : R[X]) : natTrailingDegree (-p) = natTrailingDegree p := by
  simp [natTrailingDegree]

@[simp]
theorem natTrailingDegree_intCast (n : ℤ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_intCast, natTrailingDegree_C]

alias natTrailingDegree_int_cast := natTrailingDegree_intCast

end Ring

section Semiring

variable [Semiring R]

def nextCoeffUp (p : R[X]) : R :=
  if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)

@[simp] lemma nextCoeffUp_zero : nextCoeffUp (0 : R[X]) = 0 := by simp [nextCoeffUp]

@[simp]
theorem nextCoeffUp_C_eq_zero (c : R) : nextCoeffUp (C c) = 0 := by
  rw [nextCoeffUp]
  simp

theorem nextCoeffUp_of_constantCoeff_eq_zero (p : R[X]) (hp : coeff p 0 = 0) :
    nextCoeffUp p = p.coeff (p.natTrailingDegree + 1) := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  · rw [nextCoeffUp, if_neg (natTrailingDegree_ne_zero.2 ⟨hp₀, hp⟩)]

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]}

theorem coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt
    (h : trailingDegree p < trailingDegree q) : coeff q (natTrailingDegree p) = 0 :=
  coeff_eq_zero_of_lt_trailingDegree <| natTrailingDegree_le_trailingDegree.trans_lt h

-- DISSOLVED: ne_zero_of_trailingDegree_lt

-- DISSOLVED: natTrailingDegree_eq_zero_of_constantCoeff_ne_zero

namespace Monic

lemma eq_X_pow_iff_natDegree_le_natTrailingDegree (h₁ : p.Monic) :
    p = X ^ p.natDegree ↔ p.natDegree ≤ p.natTrailingDegree := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · nontriviality R
    rw [h, natTrailingDegree_X_pow, ← h]
  · ext n
    rw [coeff_X_pow]
    obtain hn | rfl | hn := lt_trichotomy n p.natDegree
    · rw [if_neg hn.ne, coeff_eq_zero_of_lt_natTrailingDegree (hn.trans_le h)]
    · simpa only [if_pos rfl] using h₁.leadingCoeff
    · rw [if_neg hn.ne', coeff_eq_zero_of_natDegree_lt hn]

lemma eq_X_pow_iff_natTrailingDegree_eq_natDegree (h₁ : p.Monic) :
    p = X ^ p.natDegree ↔ p.natTrailingDegree = p.natDegree :=
  h₁.eq_X_pow_iff_natDegree_le_natTrailingDegree.trans (natTrailingDegree_le_natDegree p).ge_iff_eq

alias ⟨_, eq_X_pow_of_natTrailingDegree_eq_natDegree⟩ := eq_X_pow_iff_natTrailingDegree_eq_natDegree

end Monic

end Semiring

end Polynomial
