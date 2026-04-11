/-
Released under MIT license.
-/
import Val.Analysis.Complex

/-!
# Val α: Meromorphic Functions

Meromorphic functions, poles, residues, order of poles and zeros.
Meromorphic functions are ratios of holomorphic functions.
Division is contents ÷ contents = contents. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Meromorphic Function
-- ============================================================================

/-- A meromorphic function is a ratio of two holomorphic functions.
    Both numerator and denominator are contents. -/
def meromorphicApply [Mul α] (invF : α → α) (numF denomF : α → α) (z : α) : α :=
  numF z * invF (denomF z)

theorem meromorphic_contents [Mul α] (invF : α → α) (numF denomF : α → α) (z : α) :
    (contents (meromorphicApply invF numF denomF z) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Poles
-- ============================================================================

/-- Order of a pole: contents value. -/
theorem pole_order_contents (order : α) :
    (contents order : Val α) ≠ origin := by intro h; cases h

/-- At a pole of order n, f(z) = g(z)/(z-a)^n where g(a) ≠ 0 in α.
    In Val α: g(a) is contents. (z-a)^n is contents. Division is contents. -/
def poleExpansion [Add α] [Mul α] [Neg α] (invF : α → α) (g : α → α)
    (a z : α) (powF : α → α → α) (n : α) : α :=
  g z * invF (powF (z + -(a)) n)

theorem pole_expansion_contents [Add α] [Mul α] [Neg α] (invF : α → α)
    (g : α → α) (a z : α) (powF : α → α → α) (n : α) :
    (contents (poleExpansion invF g a z powF n) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Zeros of Meromorphic Functions
-- ============================================================================

/-- Order of a zero: contents value. -/
theorem zero_order_contents (order : α) :
    (contents order : Val α) ≠ origin := by intro h; cases h

/-- At a zero of order m, f(z) = (z-a)^m · g(z) where g(a) ≠ 0 in α. -/
def zeroExpansion [Add α] [Mul α] [Neg α] (g : α → α)
    (a z : α) (powF : α → α → α) (m : α) : α :=
  powF (z + -(a)) m * g z

theorem zero_expansion_contents [Add α] [Mul α] [Neg α]
    (g : α → α) (a z : α) (powF : α → α → α) (m : α) :
    (contents (zeroExpansion g a z powF m) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Residue Computation
-- ============================================================================

/-- Residue at a simple pole: Res(f, a) = lim_{z→a} (z-a)·f(z). Contents. -/
def simpleResidue [Add α] [Mul α] [Neg α]
    (invF : α → α) (numF denomF : α → α) (a : α) (limF : (α → α) → α → α) : α :=
  limF (fun z => (z + -(a)) * meromorphicApply invF numF denomF z) a

theorem simpleResidue_contents [Add α] [Mul α] [Neg α]
    (invF : α → α) (numF denomF : α → α) (a : α) (limF : (α → α) → α → α) :
    (contents (simpleResidue invF numF denomF a limF) : Val α) ≠ origin := by intro h; cases h

/-- Higher order residue: (1/(n-1)!) · lim d^(n-1)/dz^(n-1) [(z-a)^n · f(z)]. -/
def higherResidue [Add α] [Mul α] [Neg α]
    (invF : α → α) (f : α → α) (a : α) (n : α) (factorialInvF : α → α)
    (derivF : (α → α) → α → α → α) (powF : α → α → α)
    (limF : (α → α) → α → α) : α :=
  factorialInvF n * limF (fun z => derivF (fun w => powF (w + -(a)) n * f w) z n) a

theorem higherResidue_contents [Add α] [Mul α] [Neg α]
    (invF : α → α) (f : α → α) (a : α) (n : α) (factorialInvF : α → α)
    (derivF : (α → α) → α → α → α) (powF : α → α → α)
    (limF : (α → α) → α → α) :
    (contents (higherResidue invF f a n factorialInvF derivF powF limF) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Partial Fractions
-- ============================================================================

/-- Partial fraction term: Res(f, aₖ) / (z - aₖ). Contents ÷ contents. -/
def partialFractionTerm [Add α] [Mul α] [Neg α]
    (invF : α → α) (res : α) (pole z : α) : α :=
  res * invF (z + -(pole))

theorem partialFraction_contents [Add α] [Mul α] [Neg α]
    (invF : α → α) (res : α) (pole z : α) :
    (contents (partialFractionTerm invF res pole z) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Mittag-Leffler Theorem
-- ============================================================================

/-- Mittag-Leffler: meromorphic function with prescribed singularities.
    The function maps contents to contents. -/
theorem mittag_leffler_contents (f : α → α) (z : α) :
    (contents (f z) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Removable Singularity
-- ============================================================================

/-- Riemann's removable singularity theorem: extend the function at a.
    The extended function maps contents to contents. -/
def removeSingularity [DecidableEq α] (f : α → α) (a : α) (limitVal : α) : α → α :=
  fun z => if z = a then limitVal else f z

theorem removeSingularity_at [DecidableEq α] (f : α → α) (a : α) (limitVal : α) :
    (contents (removeSingularity f a limitVal a) : Val α) = contents limitVal := by
  simp [removeSingularity]

end Val
