/-
Released under MIT license.
-/
import Origin.Core

/-!
# Measure Theory on Option α (Core-based)

Val/MeasureTheory.lean: 377 lines. σ-algebras, measures, integration,
Radon-Nikodym, Fubini, probability, martingales, kernels, entropy.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. σ-ALGEBRA
-- ============================================================================

structure SigmaAlgebra (α : Type u) where
  measurable : (α → Prop) → Prop
  empty_mem : measurable (fun _ => False)
  compl_mem : ∀ S, measurable S → measurable (fun a => ¬S a)
  union_mem : ∀ (f : Nat → α → Prop), (∀ n, measurable (f n)) →
    measurable (fun a => ∃ n, f n a)

theorem sigma_full_mem (σ : SigmaAlgebra α) : σ.measurable (fun _ => True) := by
  have h := σ.compl_mem _ σ.empty_mem
  simp [not_false_eq_true] at h; exact h

-- ============================================================================
-- 2. MEASURES: null vs none
-- ============================================================================

variable {S : Type u}

/-- Null set: measure is some(zero). Not none. -/
def isNull (μ : S → Option α) (zero : α) (s : S) : Prop := μ s = some zero

/-- Null is not none — the key disambiguation. -/
theorem null_ne_none (μ : S → Option α) (zero : α) (s : S)
    (h : isNull μ zero s) : μ s ≠ none := by rw [h]; simp

-- ============================================================================
-- 3. INTEGRATION
-- ============================================================================

/-- Simple function integral: weighted sum of values. -/
def simpleIntegral [Mul α] [Add α] : List α → List α → Option α
  | [], _ => none
  | _, [] => none
  | v :: vs, w :: ws =>
    some (v * w) + simpleIntegral vs ws

-- integral none/some: Core.lean's @[simp] set handles all cases.

-- ============================================================================
-- 4. PROBABILITY
-- ============================================================================

def IsProbabilityMeasure (μ : S → Option α) (total : S) (one : α) : Prop :=
  μ total = some one

-- ============================================================================
-- 5. INDEPENDENCE
-- ============================================================================

def AreIndependent [Mul α] (pA pB pAB : α) : Prop := pAB = pA * pB

-- ============================================================================
-- 6. MARTINGALES
-- ============================================================================

def IsMartingale (X : Nat → Option α) (ceF : Nat → α → α) : Prop :=
  ∀ n a, X n = some a → Option.map (ceF n) (X (n + 1)) = some a

-- KL divergence is multiplication on Option: just use * from Core.
-- None absorbs (mul, add): Core.lean's @[simp] set handles all cases.
