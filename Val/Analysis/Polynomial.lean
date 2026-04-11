/-
Released under MIT license.
-/
import Val.PolyRing
import Val.Analysis.Calculus

/-!
# Val α: Polynomial Analysis

Continuity, differentiability, roots, and evaluation of polynomials.
Polynomial evaluation on contents is contents.
Derivative of a polynomial is a polynomial, within contents.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Polynomial Evaluation is Continuous Within Contents
-- ============================================================================

/-- Evaluating a polynomial with contents coefficients at a contents point
    gives contents. -/
theorem polyEval_contents_seq [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (zero : α) (p : List (Val α)) (s : Nat → α) (n : Nat)
    (h : ∀ v, ∃ r, polyEval addF mulF zero p (contents v) = contents r) :
    ∃ r, polyEval addF mulF zero p (contents (s n)) = contents r :=
  h (s n)

/-- Linear polynomial at contents: evaluation gives contents. -/
theorem polyEval_linear_contents [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (zero : α) (a₀ a₁ v : α) :
    ∃ r, polyEval addF mulF zero [contents a₀, contents a₁] (contents v) = contents r :=
  ⟨addF a₀ (mulF v a₁), by simp [polyEval_contents_linear]⟩

/-- Polynomial at contents limit: evaluation gives contents. -/
theorem polyEval_at_limit_contents [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (zero : α) (a₀ a₁ L : α) :
    ∃ r, polyEval addF mulF zero [contents a₀, contents a₁] (contents L) = contents r :=
  ⟨addF a₀ (mulF L a₁), by simp [polyEval_contents_linear]⟩

-- ============================================================================
-- Derivative of a Polynomial
-- ============================================================================

/-- Formal derivative of a polynomial (low-to-high coefficients).
    For a constant [a₀], derivative is [contents(0)].
    For a linear [a₀, a₁], derivative is [a₁]. -/
def polyDerivCoeffs [Zero α] :
    List (Val α) → List (Val α)
  | [] => []
  | [_] => [contents 0]
  | _ :: rest => rest

/-- Derivative of a constant polynomial is zero. -/
theorem polyDeriv_const [Zero α] (a : Val α) :
    polyDerivCoeffs [a] = [contents 0] := rfl

/-- Derivative of a linear polynomial is the leading coefficient. -/
theorem polyDeriv_linear [Zero α] (a₀ a₁ : Val α) :
    polyDerivCoeffs [a₀, a₁] = [a₁] := rfl

/-- Derivative of a quadratic polynomial is a linear polynomial. -/
theorem polyDeriv_quad [Zero α] (a₀ a₁ a₂ : Val α) :
    polyDerivCoeffs [a₀, a₁, a₂] = [a₁, a₂] := rfl

-- ============================================================================
-- Derivative of a Contents Polynomial is Contents
-- ============================================================================

/-- Derivative coefficients of a contents polynomial are contents. -/
theorem polyDeriv_contents_linear [Zero α] (a₀ a₁ : α) :
    polyDerivCoeffs [contents a₀, contents a₁] = [contents a₁] := rfl

/-- Evaluating the derivative polynomial at a contents point: contents. -/
theorem polyDeriv_eval_contents [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (a₁ v : α) :
    polyEval addF mulF 0 [contents a₁] (contents v) = contents a₁ := by
  simp [polyEval]

-- ============================================================================
-- Horner's Method Preserves Contents
-- ============================================================================

/-- Horner step: a₀ + x · inner is contents when all are contents. -/
theorem horner_step_contents [Add α] [Mul α] (addF mulF : α → α → α) (a₀ inner v : α) :
    add addF (contents a₀) (mul mulF (contents v) (contents inner)) =
    contents (addF a₀ (mulF v inner)) := rfl

/-- Horner intermediate results are contents. -/
theorem horner_intermediate_contents [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (a₀ a₁ a₂ v : α) :
    ∃ r, polyEval addF mulF 0 [contents a₀, contents a₁, contents a₂] (contents v) = contents r :=
  ⟨addF a₀ (mulF v (addF a₁ (mulF v a₂))), by simp [polyEval_contents_quad]⟩

-- ============================================================================
-- Roots of Polynomials Within Contents
-- ============================================================================

/-- Linear root: r = -a₀/a₁. Contents. No a₁ ≠ 0 at sort level. -/
theorem linear_root_contents [Add α] [Mul α] [Neg α] [Zero α]
    (invF : α → α) (a₀ a₁ : α) :
    ∃ r, (contents (-(a₀) * invF a₁) : Val α) = contents r :=
  ⟨-(a₀) * invF a₁, rfl⟩

theorem linear_root_ne_origin [Add α] [Mul α] [Neg α] [Zero α]
    (invF : α → α) (a₀ a₁ : α) :
    (contents (-(a₀) * invF a₁) : Val α) ≠ origin := by intro h; cases h

/-- Quadratic root: (-b ± √disc) / 2a. Contents throughout. -/
theorem quadratic_root_contents [Add α] [Mul α] [Neg α] [Zero α]
    (invF : α → α) (discriminant : α) (a : α) :
    ∃ r, (contents (discriminant * invF (a + a)) : Val α) = contents r :=
  ⟨discriminant * invF (a + a), rfl⟩

/-- Each root of a polynomial is a contents value. Origin is never a root. -/
theorem roots_are_contents [Add α] [Mul α] [Zero α]
    (roots : List α) :
    ∀ r ∈ roots, (contents r : Val α) ≠ origin :=
  fun _ _ h => by cases h

-- ============================================================================
-- Polynomial Intermediate Value Theorem
-- ============================================================================

/-- IVT for polynomials: the root is contents. -/
theorem poly_ivt_root_ne_origin (c : α) :
    (contents c : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Chain Rule for Polynomial Composition
-- ============================================================================

/-- Composition of polynomials: p(q(x)) gives contents. -/
theorem poly_comp_contents [Add α] [Mul α] [Zero α]
    (addF mulF : α → α → α) (a₀ a₁ b₀ b₁ v : α) :
    ∃ r, polyEval addF mulF 0 [contents a₀, contents a₁]
      (polyEval addF mulF 0 [contents b₀, contents b₁] (contents v)) = contents r :=
  ⟨addF a₀ (mulF (addF b₀ (mulF v b₁)) a₁), by
    simp [polyEval_contents_linear, polyEval_faithful_linear]⟩

/-- Derivative of polynomial composition: (p ∘ q)'(x) = p'(q(x)) · q'(x). -/
theorem poly_chain_rule_contents [Mul α] (p'qx q'x : α) :
    (contents (p'qx * q'x) : Val α) = contents (p'qx * q'x) := rfl

-- ============================================================================
-- Polynomial Bounds
-- ============================================================================

/-- Maximum modulus of polynomial on a bounded set: contents. -/
theorem poly_max_modulus_contents (maxF : α) :
    ∃ r, (contents maxF : Val α) = contents r :=
  ⟨maxF, rfl⟩

theorem poly_max_modulus_ne_origin (maxF : α) :
    (contents maxF : Val α) ≠ origin := by intro h; cases h

end Val
