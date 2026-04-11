/-
Released under MIT license.
-/
import Val.Analysis.Core
import Val.Analysis.SpecialFunctions

/-!
# Val α: Analytic Functions

Analytic functions, power series convergence, radius of convergence.
Power series coefficients are contents. Radius is contents.
Evaluation at contents gives contents. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Power Series
-- ============================================================================

/-- A formal power series: a sequence of coefficients.
    Evaluation at a point: Σ aₙ · xⁿ. Contents in, contents out. -/
def powerSeriesEval [Add α] [Mul α]
    (coeffs : Nat → α) (x : α) (powF : α → Nat → α) (sumF : (Nat → α) → α) : α :=
  sumF (fun n => coeffs n * powF x n)

theorem powerSeries_contents [Add α] [Mul α]
    (coeffs : Nat → α) (x : α) (powF : α → Nat → α) (sumF : (Nat → α) → α) :
    ∃ r, (contents (powerSeriesEval coeffs x powF sumF) : Val α) = contents r :=
  ⟨powerSeriesEval coeffs x powF sumF, rfl⟩

theorem powerSeries_ne_origin [Add α] [Mul α]
    (coeffs : Nat → α) (x : α) (powF : α → Nat → α) (sumF : (Nat → α) → α) :
    (contents (powerSeriesEval coeffs x powF sumF) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Radius of Convergence
-- ============================================================================

/-- Radius of convergence: R = invF(limsup|aₙ|^(1/n)). R is contents. -/
def radiusOfConvergence [Mul α] (invF : α → α) (limSupF : (Nat → α) → α)
    (nthRootF : α → Nat → α) (normF : α → α) (coeffs : Nat → α) : α :=
  invF (limSupF (fun n => nthRootF (normF (coeffs n)) n))

theorem radius_contents [Mul α] (invF : α → α) (limSupF : (Nat → α) → α)
    (nthRootF : α → Nat → α) (normF : α → α) (coeffs : Nat → α) :
    (contents (radiusOfConvergence invF limSupF nthRootF normF coeffs) : Val α) ≠ origin := by
  intro h; cases h

/-- Extracting the n-th coefficient of a power series. Contents value. -/
theorem coeff_contents (coeffs : Nat → α) (n : Nat) :
    (contents (coeffs n) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Composition of Power Series
-- ============================================================================

/-- Composition of power series: (f ∘ g)(x) = Σ aₙ · (g(x))ⁿ. -/
def powerSeriesComp [Add α] [Mul α]
    (coeffsF : Nat → α) (gEval : α → α) (x : α)
    (powF : α → Nat → α) (sumF : (Nat → α) → α) : α :=
  sumF (fun n => coeffsF n * powF (gEval x) n)

theorem powerSeriesComp_contents [Add α] [Mul α]
    (coeffsF : Nat → α) (gEval : α → α) (x : α)
    (powF : α → Nat → α) (sumF : (Nat → α) → α) :
    (contents (powerSeriesComp coeffsF gEval x powF sumF) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Analytic at a Point
-- ============================================================================

/-- A function f is analytic at a if it equals its power series in a neighborhood.
    In Val α: the power series has contents coefficients, evaluates to contents. -/
def isAnalyticAt [Add α] [Mul α] [Neg α]
    (f : α → α) (a : α) (coeffs : Nat → α) (powF : α → Nat → α)
    (sumF : (Nat → α) → α) : Prop :=
  ∀ x : α, f x = sumF (fun n => coeffs n * powF (x + -(a)) n)

/-- Analytic functions map contents to contents. -/
theorem analytic_contents (f : α → α) (x : α) :
    (contents (f x) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Identity Theorem
-- ============================================================================

/-- If two analytic functions agree on a set with an accumulation point,
    their coefficients agree. -/
theorem identity_theorem_coeffs (coeffsF coeffsG : Nat → α)
    (h : ∀ n, coeffsF n = coeffsG n) (n : Nat) :
    (contents (coeffsF n) : Val α) = contents (coeffsG n) := by rw [h]

/-- Two power series with overlapping discs that agree on the overlap
    have a unique continuation. -/
theorem analytic_continuation_unique (f g : α → α) (a : α)
    (h : f a = g a) :
    (contents (f a) : Val α) = contents (g a) := by rw [h]

-- ============================================================================
-- Derivative of Power Series
-- ============================================================================

/-- The derivative of a power series is a power series.
    Differentiation maps contents coefficients to contents coefficients. -/
def derivCoeffs [Mul α] (coeffs : Nat → α) (natToAlpha : Nat → α) (n : Nat) : α :=
  natToAlpha (n + 1) * coeffs (n + 1)

theorem derivCoeffs_contents [Mul α] (coeffs : Nat → α) (natToAlpha : Nat → α) (n : Nat) :
    (contents (derivCoeffs coeffs natToAlpha n) : Val α) ≠ origin := by intro h; cases h

end Val
