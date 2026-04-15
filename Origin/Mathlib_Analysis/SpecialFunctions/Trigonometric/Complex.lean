/-
Extracted from Analysis/SpecialFunctions/Trigonometric/Complex.lean
Genuine: 21 of 26 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.

Several facts about the real trigonometric functions have the proofs deferred here, rather than
`Analysis.SpecialFunctions.Trigonometric.Basic`,
as they are most easily proved by appealing to the corresponding fact for complex trigonometric
functions, or require additional imports which are not available in that file.
-/

noncomputable section

namespace Complex

open Set Filter

open scoped Real

theorem cos_eq_zero_iff {θ : ℂ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2 := by
  have h : (exp (θ * I) + exp (-θ * I)) / 2 = 0 ↔ exp (2 * θ * I) = -1 := by
    rw [@div_eq_iff _ _ (exp (θ * I) + exp (-θ * I)) 2 0 two_ne_zero, zero_mul,
      add_eq_zero_iff_eq_neg, neg_eq_neg_one_mul, ← div_eq_iff (exp_ne_zero _), ← exp_sub]
    ring_nf
  rw [cos, h, ← exp_pi_mul_I, exp_eq_exp_iff_exists_int, mul_right_comm]
  refine exists_congr fun x => ?_
  refine (iff_of_eq <| congr_arg _ ?_).trans (mul_right_inj' <| mul_ne_zero two_ne_zero I_ne_zero)
  ring

-- DISSOLVED: cos_ne_zero_iff

theorem sin_eq_zero_iff {θ : ℂ} : sin θ = 0 ↔ ∃ k : ℤ, θ = k * π := by
  rw [← Complex.cos_sub_pi_div_two, cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    use k + 1
    simp [eq_add_of_sub_eq hk]
    ring
  · rintro ⟨k, rfl⟩
    use k - 1
    simp
    ring

-- DISSOLVED: sin_ne_zero_iff

theorem tan_eq_zero_iff {θ : ℂ} : tan θ = 0 ↔ ∃ k : ℤ, k * π / 2 = θ := by
  rw [tan, div_eq_zero_iff, ← mul_eq_zero, ← mul_right_inj' two_ne_zero, mul_zero,
    ← mul_assoc, ← sin_two_mul, sin_eq_zero_iff]
  simp [field, mul_comm, eq_comm]

-- DISSOLVED: tan_ne_zero_iff

theorem tan_int_mul_pi_div_two (n : ℤ) : tan (n * π / 2) = 0 :=
  tan_eq_zero_iff.mpr (by use n)

-- DISSOLVED: tan_eq_zero_iff'

set_option linter.flexible false in -- Non-terminal simp, used to be field_simp

theorem cos_eq_cos_iff {x y : ℂ} : cos x = cos y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
  calc
    cos x = cos y ↔ cos x - cos y = 0 := sub_eq_zero.symm
    _ ↔ -2 * sin ((x + y) / 2) * sin ((x - y) / 2) = 0 := by rw [cos_sub_cos]
    _ ↔ sin ((x + y) / 2) = 0 ∨ sin ((x - y) / 2) = 0 := by simp [(by simp : (2 : ℂ) ≠ 0)]
    _ ↔ sin ((x - y) / 2) = 0 ∨ sin ((x + y) / 2) = 0 := or_comm
    _ ↔ (∃ k : ℤ, y = 2 * k * π + x) ∨ ∃ k : ℤ, y = 2 * k * π - x := by
      apply or_congr <;>
        simp [field, sin_eq_zero_iff, eq_sub_iff_add_eq',
          sub_eq_iff_eq_add, mul_comm (2 : ℂ), mul_right_comm _ (2 : ℂ)]
      constructor <;> · rintro ⟨k, rfl⟩; use -k; simp
    _ ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x := exists_or.symm

theorem sin_eq_sin_iff {x y : ℂ} :
    sin x = sin y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x := by
  simp only [← Complex.cos_sub_pi_div_two, cos_eq_cos_iff, sub_eq_iff_eq_add]
  refine exists_congr fun k => or_congr ?_ ?_ <;> refine Eq.congr rfl ?_ <;> simp [field] <;> ring

theorem cos_eq_one_iff {x : ℂ} : cos x = 1 ↔ ∃ k : ℤ, k * (2 * π) = x := by
  rw [← cos_zero, eq_comm, cos_eq_cos_iff]
  simp [mul_assoc, mul_left_comm, eq_comm]

theorem cos_eq_neg_one_iff {x : ℂ} : cos x = -1 ↔ ∃ k : ℤ, π + k * (2 * π) = x := by
  rw [← neg_eq_iff_eq_neg, ← cos_sub_pi, cos_eq_one_iff]
  simp only [eq_sub_iff_add_eq']

theorem sin_eq_one_iff {x : ℂ} : sin x = 1 ↔ ∃ k : ℤ, π / 2 + k * (2 * π) = x := by
  rw [← cos_sub_pi_div_two, cos_eq_one_iff]
  simp only [eq_sub_iff_add_eq']

theorem sin_eq_neg_one_iff {x : ℂ} : sin x = -1 ↔ ∃ k : ℤ, -(π / 2) + k * (2 * π) = x := by
  rw [← neg_eq_iff_eq_neg, ← cos_add_pi_div_two, cos_eq_one_iff]
  simp only [← sub_eq_neg_add, sub_eq_iff_eq_add]

theorem tan_add {x y : ℂ}
    (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) ∨
      (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  rcases h with (⟨h1, h2⟩ | ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩)
  · rw [tan, sin_add, cos_add, ←
      div_div_div_cancel_right₀ (mul_ne_zero (cos_ne_zero_iff.mpr h1) (cos_ne_zero_iff.mpr h2)),
      add_div, sub_div]
    simp only [← div_mul_div_comm, tan, mul_one, one_mul, div_self (cos_ne_zero_iff.mpr h1),
      div_self (cos_ne_zero_iff.mpr h2)]
  · haveI t := tan_int_mul_pi_div_two
    obtain ⟨hx, hy, hxy⟩ := t (2 * k + 1), t (2 * l + 1), t (2 * k + 1 + (2 * l + 1))
    simp only [Int.cast_add, Int.cast_two, Int.cast_mul, Int.cast_one] at hx hy hxy
    rw [hx, hy, add_zero, zero_div, mul_div_assoc, mul_div_assoc, ←
      add_mul (2 * (k : ℂ) + 1) (2 * l + 1) (π / 2), ← mul_div_assoc, hxy]

theorem tan_add' {x y : ℂ}
    (h : (∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  tan_add (Or.inl h)

theorem tan_sub {x y : ℂ}
    (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) ∨
      (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2) :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) := by
  have := tan_add (x := x) (y := -y) <| by
    rcases h with ⟨x_ne, minus_y_ne⟩ | ⟨x_eq, minus_y_eq⟩
    · refine .inl ⟨x_ne, fun l => ?_⟩
      rw [Ne, neg_eq_iff_eq_neg]
      convert minus_y_ne (-l - 1) using 2
      push_cast
      ring
    · refine .inr ⟨x_eq, ?_⟩
      rcases minus_y_eq with ⟨l, rfl⟩
      use -l - 1
      push_cast
      ring
  rw [tan_neg] at this
  convert this using 2
  ring

theorem tan_sub' {x y : ℂ}
    (h : (∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) :=
  tan_sub (Or.inl h)

theorem tan_two_mul {z : ℂ} : tan (2 * z) = (2 : ℂ) * tan z / ((1 : ℂ) - tan z ^ 2) := by
  by_cases! h : ∀ k : ℤ, z ≠ (2 * k + 1) * π / 2
  · rw [two_mul, two_mul, sq, tan_add (Or.inl ⟨h, h⟩)]
  · rw [two_mul, two_mul, sq, tan_add (Or.inr ⟨h, h⟩)]

theorem tan_add_mul_I {x y : ℂ}
    (h :
      ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y * I ≠ (2 * l + 1) * π / 2) ∨
        (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y * I = (2 * l + 1) * π / 2) :
    tan (x + y * I) = (tan x + tanh y * I) / (1 - tan x * tanh y * I) := by
  rw [tan_add h, tan_mul_I, mul_assoc]

theorem tan_eq {z : ℂ}
    (h :
      ((∀ k : ℤ, (z.re : ℂ) ≠ (2 * k + 1) * π / 2) ∧
          ∀ l : ℤ, (z.im : ℂ) * I ≠ (2 * l + 1) * π / 2) ∨
        (∃ k : ℤ, (z.re : ℂ) = (2 * k + 1) * π / 2) ∧
          ∃ l : ℤ, (z.im : ℂ) * I = (2 * l + 1) * π / 2) :
    tan z = (tan z.re + tanh z.im * I) / (1 - tan z.re * tanh z.im * I) := by
  convert tan_add_mul_I h; exact (re_add_im z).symm

lemma tan_eq_zero_of_cos_eq_zero {x} (h : cos x = 0) : tan x = 0 := by
  obtain ⟨k, hxk⟩ := cos_eq_zero_iff.mp h
  exact tan_eq_zero_iff.mpr ⟨2 * k + 1, by simp [hxk]⟩

theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq (x : ℂ) (h : cos x ≠ -1) :
    cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) := by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, cos_two_mul']
  have : cos (x / 2) ≠ 0 := by grind [cos_ne_zero_iff, cos_eq_neg_one_iff]
  rw [div_eq_mul_inv (1 - tan (x / 2) ^ 2) (1 + tan (x / 2) ^ 2), inv_one_add_tan_sq this,
    ← tan_mul_cos this]
  ring

theorem sin_eq_two_mul_tan_half_div_one_add_tan_half_sq (x : ℂ) :
    sin x = (2 * tan (x / 2)) / (1 + tan (x / 2) ^ 2) := by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, sin_two_mul]
  by_cases h : cos (x / 2) = 0
  · simp [h, tan_eq_zero_of_cos_eq_zero]
  · rw [div_eq_mul_inv (2 * tan (x / 2)) (1 + tan (x / 2) ^ 2), inv_one_add_tan_sq h,
      ← tan_mul_cos h]
    ring

theorem tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq (x : ℂ) :
    tan x = (2 * tan (x / 2)) / (1 - tan (x / 2) ^ 2) := by
  conv_lhs => rw [← mul_div_cancel₀ x two_ne_zero, tan_two_mul]

open scoped Topology

-- DISSOLVED: continuousOn_tan
