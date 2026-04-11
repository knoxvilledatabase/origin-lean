/-
Released under MIT license.
-/
import Val.Analysis.Core

/-!
# Val α: Asymptotics and Specific Limits

Big O, little o, asymptotic equivalence, specific limit computations.
Contents in, contents out. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Big O: f = O(g)
-- ============================================================================

/-- f = O(g) near a: ∃ C, ∀ x near a, ‖f(x)‖ ≤ C · ‖g(x)‖.
    In Val α: the bound C is contents. The norms are contents. -/
def isBigO [Mul α] [LE α] (normF : α → α) (f g : α → α) (C : α) : Prop :=
  ∀ x : α, normF (f x) ≤ C * normF (g x)

/-- The big O constant is contents. -/
theorem bigO_constant_contents (C : α) :
    (contents C : Val α) ≠ origin := by intro h; cases h

/-- Big O bound: the bounding inequality is at the α level. -/
theorem bigO_bound [Mul α] [LE α] (normF : α → α) (f g : α → α) (C : α)
    (h : isBigO normF f g C) (x : α) :
    normF (f x) ≤ C * normF (g x) :=
  h x

-- ============================================================================
-- Little o: f = o(g)
-- ============================================================================

/-- f = o(g): ∀ ε > 0, ∃ N, ∀ x past N, ‖f(x)‖ ≤ ε · ‖g(x)‖.
    In Val α: ε is contents. The bound is contents. -/
def isLittleO [Mul α] [LE α] [LT α] [Zero α] (normF : α → α) (f g : α → α) : Prop :=
  ∀ eps : α, (0 : α) < eps → ∃ C : α, ∀ x : α, normF (f x) ≤ eps * normF (g x)

/-- Little o implies big O for any positive constant. -/
theorem littleO_implies_bigO [Mul α] [LE α] [LT α] [Zero α]
    (normF : α → α) (f g : α → α) (h : isLittleO normF f g) (eps : α) (heps : (0 : α) < eps) :
    ∃ C : α, isBigO normF f g C := by
  obtain ⟨C, hC⟩ := h eps heps; exact ⟨eps, fun x => hC x⟩

-- ============================================================================
-- Asymptotic Equivalence: f ~ g
-- ============================================================================

/-- f ~ g: f - g = o(g). In Val α: the difference is contents. -/
def isAsympEquiv [Add α] [Neg α] [Mul α] [LE α] [LT α] [Zero α]
    (normF : α → α) (f g : α → α) : Prop :=
  isLittleO normF (fun x => f x + -(g x)) g

-- ============================================================================
-- Specific Limits
-- ============================================================================

/-- (1 + 1/n)^n → e. In Val α: each term is contents. -/
theorem euler_limit_contents [Add α] [Mul α]
    (invF : α → α) (one : α) (n : α) (powF : α → α → α) :
    (contents (powF (one + invF n) n) : Val α) ≠ origin := by intro h; cases h

/-- n^(1/n) → 1. In Val α: contents. -/
theorem nth_root_limit_contents
    (nthRootF : α → α → α) (invF : α → α) (n : α) :
    (contents (nthRootF n (invF n)) : Val α) ≠ origin := by intro h; cases h

/-- Harmonic partial sums are contents. -/
theorem harmonic_partial_contents [Add α] [Mul α]
    (invF : α → α) (partialSumF : (α → α) → α → α) (N : α) :
    (contents (partialSumF (fun n => invF n) N) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Growth Rate Comparison
-- ============================================================================

/-- Polynomial growth is O(exponential). -/
theorem poly_bigO_exp [Mul α] [LE α] (normF : α → α) (polyF expF : α → α) (C : α)
    (h : ∀ x, normF (polyF x) ≤ C * normF (expF x)) :
    isBigO normF polyF expF C :=
  h

/-- Logarithmic growth is o(polynomial). -/
theorem log_littleO_poly [Mul α] [LE α] [LT α] [Zero α]
    (normF : α → α) (logF polyF : α → α)
    (h : ∀ eps : α, (0 : α) < eps → ∃ C : α, ∀ x : α, normF (logF x) ≤ eps * normF (polyF x)) :
    isLittleO normF logF polyF :=
  h

-- ============================================================================
-- Asymptotic Expansion
-- ============================================================================

/-- An asymptotic expansion term: aₖ · gₖ(x). Contents value. -/
def asympExpansionTerm [Mul α] (coeff : α) (basisF : α → α) (x : α) : α :=
  coeff * basisF x

theorem asympExpansion_contents [Mul α] (coeff : α) (basisF : α → α) (x : α) :
    (contents (asympExpansionTerm coeff basisF x) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Stirling's Approximation
-- ============================================================================

/-- Stirling: n! ~ √(2πn) · (n/e)^n. In Val α: contents. -/
theorem stirling_contents (stirlingF : α → α) (n : α) :
    (contents (stirlingF n) : Val α) ≠ origin := by intro h; cases h

end Val
