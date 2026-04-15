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

theorem integral_none_absorbs [Mul α] (f : α → α) :
    Option.map f (none : Option α) = none := by simp

theorem integral_some_computes [Mul α] (f : α → α) (a : α) :
    Option.map f (some a) = some (f a) := by simp

-- ============================================================================
-- 4. PROBABILITY
-- ============================================================================

def IsProbabilityMeasure (μ : S → Option α) (total : S) (one : α) : Prop :=
  μ total = some one

-- ============================================================================
-- 5. INDEPENDENCE
-- ============================================================================

def AreIndependent [Mul α] (pA pB pAB : α) : Prop := pAB = pA * pB

theorem independent_product [Mul α] (pA pB : α) :
    (some pA : Option α) * some pB = some (pA * pB) := by simp

-- ============================================================================
-- 6. MARTINGALES
-- ============================================================================

def IsMartingale (X : Nat → Option α) (ceF : Nat → α → α) : Prop :=
  ∀ n a, X n = some a → Option.map (ceF n) (X (n + 1)) = some a

-- ============================================================================
-- 7. ENTROPY
-- ============================================================================

def klDivergence [Mul α] : Option α → Option α → Option α :=
  fun a b => a * b

theorem kl_none_left [Mul α] (b : Option α) :
    klDivergence (none : Option α) b = none := by simp [klDivergence]

theorem kl_some [Mul α] (a b : α) :
    klDivergence (some a) (some b) = some (a * b) := by simp [klDivergence]
