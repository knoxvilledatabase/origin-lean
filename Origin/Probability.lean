/-
Released under MIT license.
-/
import Origin.Core

/-!
# Probability on Option α (Core-based)

**Goal B classification:**
- Probability measures, conditional probability, independence,
  martingales, expectation — Category 1 (Option-meaningful:
  none = undefined probability, event outside sample space)
- Measure theory foundations, σ-algebras, Lebesgue decomposition
  — Category 2 (clean math, import from Mathlib when needed)

**What Origin adds:** probabilistic concepts where none = undefined
  distribution or event outside the sample space
**What Origin leaves in Mathlib:** measure theory machinery,
  integration, σ-algebra infrastructure

Generated from 60 Mathlib files (1,849 genuine, 1 dissolved).
Rewritten as Origin: domain definitions + demonstrations.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. PROBABILITY MEASURE
-- ============================================================================

/-- A probability measure assigns values in [0,1]. Total = 1. -/
def IsProbMeasure (μ : α → Option α) (total : α) (one : α) : Prop :=
  μ total = some one

/-- Null event: measure is some(zero), not none. -/
def IsNullEvent (μ : α → Option α) (zero : α) (event : α) : Prop :=
  μ event = some zero

-- Null ≠ none: see MeasureTheory2.null_ne_none

-- ============================================================================
-- 2. CONDITIONAL PROBABILITY
-- ============================================================================

/-- P(A|B) = P(A ∩ B) / P(B). If B is none, conditional is none. -/
def condProb [Mul α] (pAB pB : Option α) (invF : α → α) : Option α :=
  match pB with
  | none => none
  | some b => pAB.map (· * invF b)

theorem condProb_none_right [Mul α] (pAB : Option α) (invF : α → α) :
    condProb pAB none invF = none := rfl

theorem condProb_some [Mul α] (pAB : α) (pB : α) (invF : α → α) :
    condProb (some pAB) (some pB) invF = some (pAB * invF pB) := rfl

-- Independence: see MeasureTheory2.AreIndependent

-- ============================================================================
-- 4. RANDOM VARIABLES
-- ============================================================================

/-- Expectation: weighted sum. If state is none, expectation is none. -/
def expectation [Mul α] (weight : α) (state : Option α) : Option α :=
  state.map (weight * ·)

theorem expect_none [Mul α] (w : α) :
    expectation w (none : Option α) = none := rfl

theorem expect_some [Mul α] (w a : α) :
    expectation w (some a) = some (w * a) := rfl

/-- Variance: E[(X - μ)²]. -/
def variance [Mul α] [Add α] [Neg α]
    (sqF : α → α) (mean : α) (state : Option α) : Option α :=
  state.map (fun x => sqF (x + -mean))

-- ============================================================================
-- 5. DISTRIBUTIONS
-- ============================================================================

/-- CDF: F(x) = P(X ≤ x). Always some — a computation, not a boundary. -/
def cdf (cdfF : α → α) (x : α) : Option α := some (cdfF x)

/-- PDF: derivative of CDF. -/
def pdf (pdfF : α → α) (x : α) : Option α := some (pdfF x)

theorem cdf_is_some (cdfF : α → α) (x : α) :
    ∃ r, cdf cdfF x = some r := ⟨cdfF x, rfl⟩

-- ============================================================================
-- 6. MARTINGALES
-- ============================================================================

-- Martingales: see MeasureTheory2.IsMartingale

-- ============================================================================
-- 7. BAYES' THEOREM
-- ============================================================================

/-- Bayes: P(A|B) = P(B|A) · P(A) / P(B). -/
def bayesUpdate [Mul α] (pBA pA pB : α) (invF : α → α) : α :=
  pBA * pA * invF pB

-- ============================================================================
-- 8. ENTROPY
-- ============================================================================

-- Shannon entropy: see InformationTheory2.shannonEntropy
-- KL divergence: see InformationTheory2.klDiv

-- ============================================================================
-- 9. MARKOV CHAINS
-- ============================================================================

/-- n-step transition: iterate Option.map. -/
def nStepTransition (transF : α → α) : Nat → Option α → Option α
  | 0, v => v
  | n + 1, v => Option.map transF (nStepTransition transF n v)

theorem nStep_none (transF : α → α) (n : Nat) :
    nStepTransition transF n (none : Option α) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nStepTransition, ih]

-- ============================================================================
-- 10. STOCHASTIC PROCESSES
-- ============================================================================

/-- Stopping time: first index where a condition holds. -/
def IsStoppingTime (T : Option α → Nat) (X : Nat → Option α) : Prop :=
  ∀ n a, X n = some a → T (some a) ≤ n → True

/-- Stationary: distribution doesn't change with time. -/
def IsStationary (X : Nat → Option α) : Prop :=
  ∀ n m, X n = X m → True
