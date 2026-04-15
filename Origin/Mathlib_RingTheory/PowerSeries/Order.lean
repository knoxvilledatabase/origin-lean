/-
Extracted from RingTheory/PowerSeries/Order.lean
Genuine: 21 | Conflates: 0 | Dissolved: 11 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Formal power series (in one variable) - Order

The `PowerSeries.order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `PowerSeries.order` is an
additive valuation (`PowerSeries.order_mul`, `PowerSeries.min_order_le_order_add`).

We prove that if the commutative ring `R` of coefficients is an integral domain,
then the ring `R⟦X⟧` of formal power series in one variable over `R`
is an integral domain.

Given a non-zero power series `f`, `divided_by_X_pow_order f` is the power series obtained by
dividing out the largest power of X that divides `f`, that is its order. This is useful when
proving that `R⟦X⟧` is a normalization monoid, which is done in `PowerSeries.Inverse`.

-/

noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section OrderBasic

open multiplicity

variable [Semiring R] {φ : R⟦X⟧}

-- DISSOLVED: exists_coeff_ne_zero_iff_ne_zero

def order (φ : R⟦X⟧) : ℕ∞ :=
  letI := Classical.decEq R
  letI := Classical.decEq R⟦X⟧
  if h : φ = 0 then ⊤ else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)

@[simp]
theorem order_zero : order (0 : R⟦X⟧) = ⊤ :=
  dif_pos rfl

-- DISSOLVED: order_finite_iff_ne_zero

-- DISSOLVED: coeff_order

-- DISSOLVED: order_le

theorem coeff_of_lt_order (n : ℕ) (h : ↑n < order φ) : coeff R n φ = 0 := by
  contrapose! h
  exact order_le _ h

@[simp]
theorem order_eq_top {φ : R⟦X⟧} : φ.order = ⊤ ↔ φ = 0 := by
  simpa using order_finite_iff_ne_zero.not_left

theorem nat_le_order (φ : R⟦X⟧) (n : ℕ) (h : ∀ i < n, coeff R i φ = 0) : ↑n ≤ order φ := by
  by_contra H; rw [not_le] at H
  have lt_top : order φ < ⊤ := lt_top_of_lt H
  replace H : (order φ).lift lt_top < n := by simpa
  exact coeff_order lt_top (h _ H)

theorem le_order (φ : R⟦X⟧) (n : ℕ∞) (h : ∀ i : ℕ, ↑i < n → coeff R i φ = 0) :
    n ≤ order φ := by
  cases n with
  | top => simpa using ext (by simpa using h)
  | coe n =>
    convert nat_le_order φ n _
    simpa using h

-- DISSOLVED: order_eq_nat

-- DISSOLVED: order_eq

theorem min_order_le_order_add (φ ψ : R⟦X⟧) : min (order φ) (order ψ) ≤ order (φ + ψ) := by
  refine le_order _ _ ?_
  simp +contextual [coeff_of_lt_order]

private theorem order_add_of_order_eq.aux (φ ψ : R⟦X⟧) (_h : order φ ≠ order ψ)
    (H : order φ < order ψ) : order (φ + ψ) ≤ order φ ⊓ order ψ := by
  suffices order (φ + ψ) = order φ by
    rw [le_inf_iff, this]
    exact ⟨le_rfl, le_of_lt H⟩
  rw [order_eq]
  constructor
  · intro i hi
    rw [← hi] at H
    rw [(coeff _ _).map_add, coeff_of_lt_order i H, add_zero]
    exact (order_eq_nat.1 hi.symm).1
  · intro i hi
    rw [(coeff _ _).map_add, coeff_of_lt_order i hi, coeff_of_lt_order i (lt_trans hi H),
      zero_add]

theorem order_add_of_order_eq (φ ψ : R⟦X⟧) (h : order φ ≠ order ψ) :
    order (φ + ψ) = order φ ⊓ order ψ := by
  refine le_antisymm ?_ (min_order_le_order_add _ _)
  by_cases H₁ : order φ < order ψ
  · apply order_add_of_order_eq.aux _ _ h H₁
  by_cases H₂ : order ψ < order φ
  · simpa only [add_comm, inf_comm] using order_add_of_order_eq.aux _ _ h.symm H₂
  exfalso; exact h (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁))

theorem le_order_mul (φ ψ : R⟦X⟧) : order φ + order ψ ≤ order (φ * ψ) := by
  apply le_order
  intro n hn; rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases hi : ↑i < order φ
  · rw [coeff_of_lt_order i hi, zero_mul]
  by_cases hj : ↑j < order ψ
  · rw [coeff_of_lt_order j hj, mul_zero]
  rw [not_lt] at hi hj; rw [mem_antidiagonal] at hij
  exfalso
  apply ne_of_lt (lt_of_lt_of_le hn <| add_le_add hi hj)
  rw [← Nat.cast_add, hij]

alias order_mul_ge := le_order_mul

theorem order_monomial (n : ℕ) (a : R) [Decidable (a = 0)] :
    order (monomial R n a) = if a = 0 then (⊤ : ℕ∞) else n := by
  split_ifs with h
  · rw [h, order_eq_top, LinearMap.map_zero]
  · rw [order_eq]
    constructor <;> intro i hi
    · simp only [Nat.cast_inj] at hi
      rwa [hi, coeff_monomial_same]
    · simp only [Nat.cast_lt] at hi
      rw [coeff_monomial, if_neg]
      exact ne_of_lt hi

-- DISSOLVED: order_monomial_of_ne_zero

theorem coeff_mul_of_lt_order {φ ψ : R⟦X⟧} {n : ℕ} (h : ↑n < ψ.order) :
    coeff R n (φ * ψ) = 0 := by
  suffices coeff R n (φ * ψ) = ∑ p ∈ antidiagonal n, 0 by rw [this, Finset.sum_const_zero]
  rw [coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  refine mul_eq_zero_of_right (coeff R x.fst φ) (coeff_of_lt_order x.snd (lt_of_le_of_lt ?_ h))
  rw [mem_antidiagonal] at hx
  norm_cast
  omega

theorem coeff_mul_one_sub_of_lt_order {R : Type*} [CommRing R] {φ ψ : R⟦X⟧} (n : ℕ)
    (h : ↑n < ψ.order) : coeff R n (φ * (1 - ψ)) = coeff R n φ := by
  simp [coeff_mul_of_lt_order h, mul_sub]

theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (k : ℕ) (s : Finset ι)
    (φ : R⟦X⟧) (f : ι → R⟦X⟧) :
    (∀ i ∈ s, ↑k < (f i).order) → coeff R k (φ * ∏ i ∈ s, (1 - f i)) = coeff R k φ := by
  classical
  induction' s using Finset.induction_on with a s ha ih t
  · simp
  · intro t
    simp only [Finset.mem_insert, forall_eq_or_imp] at t
    rw [Finset.prod_insert ha, ← mul_assoc, mul_right_comm, coeff_mul_one_sub_of_lt_order _ t.1]
    exact ih t.2

theorem X_pow_order_dvd (h : order φ < ⊤) : X ^ (order φ).lift h ∣ φ := by
  refine ⟨PowerSeries.mk fun n => coeff R (n + (order φ).lift h) φ, ?_⟩
  ext n
  simp only [coeff_mul, coeff_X_pow, coeff_mk, boole_mul, Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  rw [Finset.filter_fst_eq_antidiagonal n ((order φ).lift h)]
  split_ifs with hn
  · simp [tsub_add_cancel_of_le hn]
  · simp only [Finset.sum_empty]
    refine coeff_of_lt_order _ ?_
    simpa using hn

theorem order_eq_emultiplicity_X {R : Type*} [Semiring R] (φ : R⟦X⟧) :
    order φ = emultiplicity X φ := by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  cases ho : order φ with
  | top => simp [hφ] at ho
  | coe n =>
    have hn : φ.order.lift (order_finite_iff_ne_zero.mpr hφ) = n := by simp [ho]
    rw [← hn, eq_comm]
    apply le_antisymm _
    · apply le_emultiplicity_of_pow_dvd
      apply X_pow_order_dvd
    · apply Order.le_of_lt_add_one
      rw [← not_le, ← Nat.cast_one, ← Nat.cast_add, ← pow_dvd_iff_le_emultiplicity]
      rintro ⟨ψ, H⟩
      have := congr_arg (coeff R n) H
      rw [← (ψ.commute_X.pow_right _).eq, coeff_mul_of_lt_order, ← hn] at this
      · exact coeff_order _ this
      · rw [X_pow_eq, order_monomial]
        split_ifs
        · simp
        · rw [← hn, ENat.coe_lt_coe]
          simp

-- DISSOLVED: divided_by_X_pow_order

-- DISSOLVED: self_eq_X_pow_order_mul_divided_by_X_pow_order

end OrderBasic

section OrderZeroNeOne

variable [Semiring R] [Nontrivial R]

@[simp]
theorem order_one : order (1 : R⟦X⟧) = 0 := by
  simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero

theorem order_zero_of_unit {f : PowerSeries R} : IsUnit f → f.order = 0 := by
  rintro ⟨⟨u, v, hu, hv⟩, hf⟩
  apply And.left
  rw [← add_eq_zero, ← hf, ← nonpos_iff_eq_zero, ← @order_one R _ _, ← hu]
  exact order_mul_ge _ _

@[simp]
theorem order_X : order (X : R⟦X⟧) = 1 := by
  simpa only [Nat.cast_one] using order_monomial_of_ne_zero 1 (1 : R) one_ne_zero

@[simp]
theorem order_X_pow (n : ℕ) : order ((X : R⟦X⟧) ^ n) = n := by
  rw [X_pow_eq, order_monomial_of_ne_zero]
  exact one_ne_zero

end OrderZeroNeOne

section OrderIsDomain

variable [CommRing R] [IsDomain R]

theorem order_mul (φ ψ : R⟦X⟧) : order (φ * ψ) = order φ + order ψ := by
  classical
  simp only [order_eq_emultiplicity_X]
  rw [emultiplicity_mul X_prime]

-- DISSOLVED: divided_by_X_pow_order_of_X_eq_one

-- DISSOLVED: divided_by_X_pow_orderMul

end OrderIsDomain

end PowerSeries

end
