/-
Extracted from FieldTheory/Differential/Basic.lean
Genuine: 8 | Conflates: 0 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Differential Fields

This file defines the logarithmic derivative `Differential.logDeriv` and proves properties of it.
This is defined algebraically, compared to `logDeriv` which is analytical.
-/

namespace Differential

open algebraMap

variable {R : Type*} [Field R] [Differential R] (a b : R)

def logDeriv : R := a′ / a

@[simp]
lemma logDeriv_zero : logDeriv (0 : R) = 0 := by
  simp [logDeriv]

@[simp]
lemma logDeriv_one : logDeriv (1 : R) = 0 := by
  simp [logDeriv]

-- DISSOLVED: logDeriv_mul

-- DISSOLVED: logDeriv_div

@[simp]
lemma logDeriv_pow (n : ℕ) (a : R) : logDeriv (a ^ n) = n * logDeriv a := by
  induction n with
  | zero => simp
  | succ n h2 =>
    obtain rfl | hb := eq_or_ne a 0
    · simp
    · rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← h2, pow_succ, logDeriv_mul] <;>
      simp [hb]

lemma logDeriv_eq_zero : logDeriv a = 0 ↔ a′ = 0 :=
  ⟨fun h ↦ by simp only [logDeriv, div_eq_zero_iff] at h; rcases h with h|h <;> simp [h],
  fun h ↦ by unfold logDeriv at *; simp [h]⟩

-- DISSOLVED: logDeriv_multisetProd

-- DISSOLVED: logDeriv_prod

lemma logDeriv_prod_of_eq_zero (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x = 0) :
    logDeriv (∏ x ∈ s, f x) = ∑ x ∈ s, logDeriv (f x) := by
  unfold logDeriv
  simp_all

lemma logDeriv_algebraMap {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logDeriv (algebraMap F K a) = algebraMap F K (logDeriv a) := by
  unfold logDeriv
  simp [deriv_algebraMap]

@[norm_cast]
lemma _root_.algebraMap.coe_logDeriv {F K : Type*} [Field F] [Field K] [Differential F]
    [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    (a : F) : logDeriv a = logDeriv (a : K) := (logDeriv_algebraMap a).symm

end Differential
