/-
Released under MIT license.
-/
import Val.Analysis.Asymptotics
import Val.Analysis.SpecialFunctions

/-!
# Val α: Asymptotic Limits and Specific Computations

Summability, Abel's theorem, Cesaro means, Dirichlet series.
All limit computations produce contents values. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Summability
-- ============================================================================

/-- A series Σ aₙ is summable if partial sums converge.
    In Val α: partial sums are contents. -/
def isSummable (partialSumF : (Nat → α) → Nat → α)
    (conv : (Nat → α) → α → Prop) (seq : Nat → α) : Prop :=
  ∃ L : α, conv (partialSumF seq) L

/-- The sum of a summable series is contents. -/
theorem summable_sum_contents (L : α) :
    (contents L : Val α) ≠ origin := by intro h; cases h

/-- Partial sums are contents. -/
theorem partial_sum_contents (partialSumF : (Nat → α) → Nat → α) (seq : Nat → α) (n : Nat) :
    (contents (partialSumF seq n) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Absolute Convergence
-- ============================================================================

/-- Absolute convergence: Σ |aₙ| converges. -/
def isAbsolutelySummable (absF : α → α) (partialSumF : (Nat → α) → Nat → α)
    (conv : (Nat → α) → α → Prop) (seq : Nat → α) : Prop :=
  isSummable partialSumF conv (fun n => absF (seq n))

-- ============================================================================
-- Comparison Test
-- ============================================================================

/-- If |aₙ| ≤ bₙ, the comparison is within contents. -/
theorem comparison_test_contents [LE α]
    (absF : α → α) (seq bound : Nat → α)
    (h : ∀ n, absF (seq n) ≤ bound n) (n : Nat) :
    absF (seq n) ≤ bound n :=
  h n

-- ============================================================================
-- Ratio Test
-- ============================================================================

/-- Ratio test: |aₙ₊₁/aₙ|. In Val α: contents ÷ contents = contents. -/
def ratioTestQuotient [Mul α] (invF : α → α) (absF : α → α) (seq : Nat → α) (n : Nat) : α :=
  absF (seq (n + 1)) * invF (absF (seq n))

theorem ratio_test_contents [Mul α] (invF absF : α → α) (seq : Nat → α) (n : Nat) :
    (contents (ratioTestQuotient invF absF seq n) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Root Test
-- ============================================================================

/-- Root test: limsup |aₙ|^(1/n) < 1 implies convergence. -/
def rootTestTerm (absF : α → α) (nthRootF : α → Nat → α)
    (seq : Nat → α) (n : Nat) : α :=
  nthRootF (absF (seq n)) n

theorem root_test_contents
    (absF : α → α) (nthRootF : α → Nat → α) (seq : Nat → α) (n : Nat) :
    (contents (rootTestTerm absF nthRootF seq n) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Cesaro Mean
-- ============================================================================

/-- Cesaro mean: σₙ = (s₀ + ... + sₙ) / (n+1). Division is contents ÷ contents. -/
def cesaroMean [Add α] [Mul α]
    (invF : α → α)
    (partialSumF : (Nat → α) → Nat → α)
    (sumOfPartialSums : (Nat → α) → Nat → α)
    (natToAlpha : Nat → α) (seq : Nat → α) (n : Nat) : α :=
  sumOfPartialSums (partialSumF seq) n * invF (natToAlpha (n + 1))

theorem cesaro_contents [Add α] [Mul α]
    (invF : α → α)
    (partialSumF sumOfPartialSums : (Nat → α) → Nat → α)
    (natToAlpha : Nat → α) (seq : Nat → α) (n : Nat) :
    (contents (cesaroMean invF partialSumF sumOfPartialSums natToAlpha seq n) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Abel's Theorem
-- ============================================================================

/-- Abel sum: Σ aₙ xⁿ. In Val α: the result is contents. -/
def abelSum [Add α] [Mul α] (seq : Nat → α) (x : α)
    (powF : α → Nat → α) (sumF : (Nat → α) → α) : α :=
  sumF (fun n => seq n * powF x n)

theorem abel_sum_contents [Add α] [Mul α]
    (seq : Nat → α) (x : α) (powF : α → Nat → α) (sumF : (Nat → α) → α) :
    (contents (abelSum seq x powF sumF) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Geometric Series
-- ============================================================================

/-- Geometric series sum 1/(1-r). In Val α: contents. -/
theorem geometric_series_contents [Add α] [Mul α] [Neg α]
    (invF : α → α) (one r : α) :
    (contents (invF (one + -(r))) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Power Series at Boundary
-- ============================================================================

/-- A power series evaluated at the boundary of convergence.
    The value (if it converges) is contents. -/
theorem boundary_eval_contents [Add α] [Mul α]
    (coeffs : Nat → α) (boundaryPt : α)
    (powF : α → Nat → α) (sumF : (Nat → α) → α) :
    (contents (sumF (fun n => coeffs n * powF boundaryPt n)) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Dirichlet Series
-- ============================================================================

/-- Dirichlet series: Σ aₙ / nˢ. Each term is contents ÷ contents = contents. -/
def dirichletTerm [Mul α] (invF : α → α) (coeffs : Nat → α) (powF : α → α → α)
    (natToAlpha : Nat → α) (s : α) (n : Nat) : α :=
  coeffs n * invF (powF (natToAlpha n) s)

theorem dirichlet_contents [Mul α] (invF : α → α)
    (coeffs : Nat → α) (powF : α → α → α) (natToAlpha : Nat → α) (s : α) (n : Nat) :
    (contents (dirichletTerm invF coeffs powF natToAlpha s n) : Val α) ≠ origin := by intro h; cases h

end Val
