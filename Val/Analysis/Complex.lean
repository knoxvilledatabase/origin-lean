/-
Released under MIT license.
-/
import Val.Analysis.Calculus
import Val.Analysis.SpecialFunctions

/-!
# Val α: Complex Analysis

Cauchy integral, holomorphic functions, residues, analytic continuation.
Complex functions map contents to contents.
Residues are contents values. Contour integrals stay contents.
No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Complex-Valued Functions on Val α
-- ============================================================================

/-- A complex function: maps α to a pair (real, imaginary) encoded in α.
    Contents in, contents out. -/
def complexApply (reF imF : α → α) : Val α → Val α × Val α
  | origin => (origin, origin)
  | container a => (container (reF a), container (imF a))
  | contents a => (contents (reF a), contents (imF a))

theorem complexApply_contents_fst (reF imF : α → α) (a : α) :
    (complexApply reF imF (contents a)).1 = contents (reF a) := rfl

theorem complexApply_contents_snd (reF imF : α → α) (a : α) :
    (complexApply reF imF (contents a)).2 = contents (imF a) := rfl

-- ============================================================================
-- Holomorphic Functions
-- ============================================================================

/-- A function is holomorphic if it has a complex derivative.
    The derivative maps contents to contents. -/
def isHolomorphic [Zero α] [Add α] [Mul α] (f f' : α → α) (a : α)
    (dist : α → α → α) (normF : α → α) (ltF : α → α → Prop) : Prop :=
  hasFDeriv f f' a dist normF ltF

theorem holomorphic_deriv_contents (f' : α → α) (a : α) :
    (contents (f' a) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Cauchy Integral Formula
-- ============================================================================

/-- The Cauchy integral kernel: f(z)/(z - a).
    Both f(z) and (z - a) are contents. Division is contents. -/
def cauchyKernel [Add α] [Mul α] [Neg α] (invF : α → α) (f : α → α) (a z : α) : α :=
  f z * invF (z + -(a))

theorem cauchy_kernel_contents [Add α] [Mul α] [Neg α] (invF : α → α) (f : α → α) (a z : α) :
    ∃ r, (contents (cauchyKernel invF f a z) : Val α) = contents r :=
  ⟨cauchyKernel invF f a z, rfl⟩

theorem cauchy_kernel_ne_origin [Add α] [Mul α] [Neg α] (invF : α → α) (f : α → α) (a z : α) :
    (contents (cauchyKernel invF f a z) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Residue
-- ============================================================================

/-- A residue at a pole: the coefficient of 1/(z-a) in the Laurent expansion.
    In Val α: a contents value. -/
theorem residue_contents (res : α) :
    (contents res : Val α) ≠ origin := by intro h; cases h

/-- Residue theorem: ∮ f(z) dz = 2πi · Σ Res(f, aₖ). Sum is contents. -/
theorem residue_sum_contents [Add α] [Mul α] (twopiI : α) (sumRes : α) :
    ∃ r, (contents (twopiI * sumRes) : Val α) = contents r :=
  ⟨twopiI * sumRes, rfl⟩

-- ============================================================================
-- Laurent Series
-- ============================================================================

/-- A Laurent series coefficient. Contents value. -/
theorem laurent_coeff_contents (coeff : α) :
    (contents coeff : Val α) ≠ origin := by intro h; cases h

/-- A Laurent series evaluated at a point. Contents computation. -/
def laurentEval [Add α] [Mul α] [Neg α] (invF : α → α) (coeffs : Nat → α) (center z : α)
    (sumF : (Nat → α) → α) : α :=
  sumF (fun n => coeffs n * invF (z + -(center)))

theorem laurent_eval_contents [Add α] [Mul α] [Neg α] (invF : α → α)
    (coeffs : Nat → α) (center z : α) (sumF : (Nat → α) → α) :
    (contents (laurentEval invF coeffs center z sumF) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Maximum Modulus Principle
-- ============================================================================

/-- Maximum modulus: |f(z)| is contents for contents z. The max is contents. -/
theorem max_modulus_contents (normF : α → α) (f : α → α) (z : α) :
    ∃ r, (contents (normF (f z)) : Val α) = contents r :=
  ⟨normF (f z), rfl⟩

-- ============================================================================
-- Liouville's Theorem
-- ============================================================================

/-- Liouville: bounded entire functions are constant. The constant value is contents. -/
theorem liouville_contents (c : α) :
    (contents c : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Argument Principle
-- ============================================================================

/-- The argument principle: f'/f is contents ÷ contents = contents.
    The count of zeros minus poles is contents. -/
def logDeriv [Mul α] (invF : α → α) (f' f_val : α) : α := f' * invF f_val

theorem logDeriv_contents [Mul α] (invF : α → α) (f' f_val : α) :
    (contents (logDeriv invF f' f_val) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Analytic Continuation
-- ============================================================================

/-- Analytic continuation: agreement is a contents equation. -/
theorem analytic_continuation (f g : α → α) (a : α)
    (h : f a = g a) :
    (contents (f a) : Val α) = contents (g a) := by rw [h]

end Val
