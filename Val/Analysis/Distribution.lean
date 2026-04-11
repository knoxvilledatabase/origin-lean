/-
Released under MIT license.
-/
import Val.Analysis.Calculus
import Val.FunctionalAnalysis

/-!
# Val α: Distributions

Distributions (generalized functions), test functions, weak derivatives.
Distributions are functionals on test functions. Contents in, contents out.
The duality pairing maps contents test functions to contents values.
No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Test Function Space
-- ============================================================================

/-- A test function: smooth with compact support. Maps contents to contents. -/
def testFnApply (phi : α → α) : Val α → Val α
  | origin => origin
  | container a => container (phi a)
  | contents a => contents (phi a)

theorem testFn_contents (phi : α → α) (a : α) :
    testFnApply phi (contents a) = contents (phi a) := rfl

theorem testFn_ne_origin (phi : α → α) (a : α) :
    testFnApply phi (contents a) ≠ (origin : Val α) := by intro h; cases h

-- ============================================================================
-- Distribution: A Continuous Linear Functional on Test Functions
-- ============================================================================

/-- A distribution T: maps test functions to scalars. T(φ) is contents. -/
def distribApply (T : (α → α) → α) (phi : α → α) : Val α :=
  contents (T phi)

theorem distrib_contents (T : (α → α) → α) (phi : α → α) :
    ∃ r, distribApply T phi = contents r := ⟨T phi, rfl⟩

theorem distrib_ne_origin (T : (α → α) → α) (phi : α → α) :
    distribApply T phi ≠ (origin : Val α) := by intro h; cases h

-- ============================================================================
-- Linearity of Distributions
-- ============================================================================

/-- Distribution is additive: T(φ + ψ) = T(φ) + T(ψ). -/
theorem distrib_add [Add α] (T : (α → α) → α)
    (hadd : ∀ phi psi : α → α, T (fun x => phi x + psi x) = T phi + T psi)
    (phi psi : α → α) :
    distribApply T (fun x => phi x + psi x) =
    contents (T phi + T psi) := by
  show contents (T (fun x => phi x + psi x)) = contents (T phi + T psi); rw [hadd]

/-- Distribution scales: T(c·φ) = c·T(φ). -/
theorem distrib_smul [Mul α] (T : (α → α) → α)
    (hsmul : ∀ (c : α) (phi : α → α), T (fun x => c * phi x) = c * T phi)
    (c : α) (phi : α → α) :
    distribApply T (fun x => c * phi x) =
    contents (c * T phi) := by
  show contents (T (fun x => c * phi x)) = contents (c * T phi); rw [hsmul]

-- ============================================================================
-- Weak Derivative
-- ============================================================================

/-- Weak derivative of a distribution: T'(φ) = -T(φ'). -/
def weakDeriv [Neg α] (T : (α → α) → α) (derivF : (α → α) → (α → α)) (phi : α → α) : α :=
  -(T (derivF phi))

theorem weakDeriv_contents [Neg α] (T : (α → α) → α) (derivF : (α → α) → (α → α)) (phi : α → α) :
    (contents (weakDeriv T derivF phi) : Val α) ≠ origin := by intro h; cases h

/-- The weak derivative distribution. -/
def weakDerivDistrib [Neg α] (T : (α → α) → α) (derivF : (α → α) → (α → α)) : (α → α) → α :=
  weakDeriv T derivF

theorem weakDerivDistrib_ne_origin [Neg α] (T : (α → α) → α) (derivF : (α → α) → (α → α)) (phi : α → α) :
    distribApply (weakDerivDistrib T derivF) phi ≠ (origin : Val α) := by intro h; cases h

-- ============================================================================
-- Delta Distribution
-- ============================================================================

/-- The Dirac delta: δₐ(φ) = φ(a). Evaluates test function at contents point. -/
def deltaDistrib (a : α) : (α → α) → α :=
  fun phi => phi a

theorem delta_contents (a : α) (phi : α → α) :
    distribApply (deltaDistrib a) phi = contents (phi a) := rfl

theorem delta_ne_origin (a : α) (phi : α → α) :
    distribApply (deltaDistrib a) phi ≠ (origin : Val α) := by intro h; cases h

-- ============================================================================
-- Convolution of Distribution with Test Function
-- ============================================================================

/-- Convolution (T * φ)(x) = T(y ↦ φ(x - y)). Contents in, contents out. -/
def distribConvolution [Add α] [Neg α] (T : (α → α) → α) (phi : α → α) (x : α) : α :=
  T (fun y => phi (x + -(y)))

theorem distribConvolution_contents [Add α] [Neg α]
    (T : (α → α) → α) (phi : α → α) (x : α) :
    (contents (distribConvolution T phi x) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Fundamental Solution
-- ============================================================================

/-- A fundamental solution E satisfies L(E) = δ for differential operator L.
    E maps contents to contents. -/
theorem fundamental_solution_contents (E : α → α) (x : α) :
    (contents (E x) : Val α) ≠ origin := by intro h; cases h

end Val
