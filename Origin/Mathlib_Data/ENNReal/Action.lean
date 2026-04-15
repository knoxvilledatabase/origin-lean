/-
Extracted from Data/ENNReal/Action.lean
Genuine: 4 of 15 | Dissolved: 2 | Infrastructure: 9
-/
import Origin.Core

/-!
# Scalar multiplication on `ℝ≥0∞`.

This file defines basic scalar actions on extended nonnegative reals, showing that
`MulAction`s, `DistribMulAction`s, `Module`s and `Algebra`s restrict from `ℝ≥0∞` to `ℝ≥0`.
-/

open Set NNReal ENNReal

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

section Actions

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): smulCommClass_left

-- INSTANCE (free from Core): smulCommClass_right

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): {M

-- INSTANCE (free from Core): {A

noncomputable example : Algebra ℝ≥0 ℝ≥0∞ := inferInstance

noncomputable example : DistribMulAction ℝ≥0ˣ ℝ≥0∞ := inferInstance

theorem coe_smul {R} (r : R) (s : ℝ≥0) [SMul R ℝ≥0] [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0]
    [IsScalarTower R ℝ≥0 ℝ≥0∞] : (↑(r • s) : ℝ≥0∞) = (r : R) • (s : ℝ≥0∞) := by
  rw [← smul_one_smul ℝ≥0 r (s : ℝ≥0∞), smul_def, smul_eq_mul, ← ENNReal.coe_mul, smul_mul_assoc,
    one_mul]

theorem smul_top {R : Type*} [Semiring R] [IsDomain R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [Module.IsTorsionFree R ℝ≥0∞] [DecidableEq R] (c : R) :
    c • ∞ = if c = 0 then 0 else ∞ := by
  rw [← smul_one_mul, mul_top']
  simp_rw [smul_eq_zero, or_iff_left one_ne_zero]

lemma nnreal_smul_lt_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y < ⊤) : x • y < ⊤ := mul_lt_top (by simp) hy

lemma nnreal_smul_ne_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y ≠ ⊤) : x • y ≠ ⊤ := mul_ne_top (by simp) hy

-- DISSOLVED: nnreal_smul_ne_top_iff

-- DISSOLVED: nnreal_smul_lt_top_iff
