/-
Released under MIT license.
-/
import Val.FunctionalAnalysis

/-!
# Val α: Spectral Theory

Operator spectra, eigenvalues, resolvent. The `‖T‖ ≠ 0` dissolution
meets eigenvalue theory. Everything stays in contents.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Eigenvalue Problem
-- ============================================================================

/-- Eigenvalue equation: T(v) = λ·v. Both sides contents. -/
theorem eigenvalue_eq (mulF : α → α → α) (T : α → α) (lambda v : α)
    (h : T v = mulF lambda v) :
    opApply T (contents v) = mul mulF (contents lambda) (contents v) := by
  simp [h]

/-- Eigenvalues are never origin when eigenvectors are contents. -/
theorem spectral_eigenvalue_ne_origin (mulF : α → α → α) (lambda v : α) :
    mul mulF (contents lambda) (contents v) ≠ origin := by simp

-- ============================================================================
-- Resolvent: (T - λI)⁻¹
-- ============================================================================

/-- Resolvent operator at λ: (T - λI)(v) = T(v) - λ·v. -/
def resolventApply (addF mulF : α → α → α) (negF : α → α)
    (T : α → α) (lambda v : α) : α :=
  addF (T v) (negF (mulF lambda v))

/-- Resolvent applied to contents is contents. -/
theorem resolvent_contents (addF mulF : α → α → α) (negF : α → α)
    (T : α → α) (lambda v : α) :
    ∃ r, (contents (resolventApply addF mulF negF T lambda v) : Val α) = contents r :=
  ⟨resolventApply addF mulF negF T lambda v, rfl⟩

/-- Resolvent never produces origin from contents inputs. -/
theorem resolvent_ne_origin (addF mulF : α → α → α) (negF : α → α)
    (T : α → α) (lambda v : α) :
    (contents (resolventApply addF mulF negF T lambda v) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Spectrum
-- ============================================================================

/-- The spectrum: predicate on α. Origin is never in the spectrum. -/
theorem spectrum_is_contents (charPolyZero : α → Prop) (lambda : α) :
    charPolyZero lambda → ∃ r, (contents lambda : Val α) = contents r :=
  fun _ => ⟨lambda, rfl⟩

/-- Contents values are always sort-available. Never origin. -/
theorem contents_not_origin (a : α) : (contents a : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Spectral Decomposition
-- ============================================================================

/-- Each spectral term λᵢ · projᵢ is contents. -/
theorem spectral_term_contents (mulF : α → α → α) (lambda proj_v : α) :
    mul mulF (contents lambda) (contents proj_v) = contents (mulF lambda proj_v) := rfl

/-- The full spectral sum: adding contents terms gives contents. -/
theorem spectral_sum_two (mulF addF : α → α → α) (l1 p1 l2 p2 : α) :
    add addF (mul mulF (contents l1) (contents p1))
             (mul mulF (contents l2) (contents p2)) =
    contents (addF (mulF l1 p1) (mulF l2 p2)) := rfl

-- ============================================================================
-- Operator Functions
-- ============================================================================

/-- f(T) applied to contents is contents. -/
theorem operator_function_contents (f T : α → α) (v : α) :
    opApply f (opApply T (contents v)) = contents (f (T v)) := rfl

/-- Operator functions never produce origin from contents. -/
theorem operator_function_ne_origin (f T : α → α) (v : α) :
    opApply f (opApply T (contents v)) ≠ (origin : Val α) := by intro h; cases h

/-- The exponential of an operator: e^T on contents is contents. -/
theorem operator_exp_contents (expT : α → α) (v : α) :
    opApply expT (contents v) = contents (expT v) := rfl

-- ============================================================================
-- Fredholm Alternative
-- ============================================================================

/-- If (T - λI)x = b is solvable, the solution x is contents. -/
theorem fredholm_solution_contents (addF mulF : α → α → α) (negF : α → α)
    (T : α → α) (lambda b x : α)
    (_ : resolventApply addF mulF negF T lambda x = b) :
    ∃ r, (contents x : Val α) = contents r := ⟨x, rfl⟩

/-- Spectral radius: contents value, never origin. -/
theorem spectral_radius_contents (radius : α) :
    (contents radius : Val α) ≠ origin := by intro h; cases h

end Val
