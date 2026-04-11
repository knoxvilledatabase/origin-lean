/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Polynomial Rings over Val α

Horner evaluation, origin propagation, contents closure.
The key finding: origin poisoning works like NaN, but by design — structural, not convention.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Polynomial Evaluation (Horner's method)
-- ============================================================================

/-- Evaluate a polynomial (low-degree first) at a point via Horner's method.
    Empty polynomial = contents(zero). -/
def polyEval (addF mulF : α → α → α) (zero : α) : List (Val α) → Val α → Val α
  | [], _ => contents zero
  | [a], _ => a
  | a :: b :: rest, x => add addF a (mul mulF x (polyEval addF mulF zero (b :: rest) x))

-- ============================================================================
-- Base Cases
-- ============================================================================

@[simp] theorem polyEval_empty (addF mulF : α → α → α) (zero : α) (x : Val α) :
    polyEval addF mulF zero [] x = contents zero := rfl

@[simp] theorem polyEval_const (addF mulF : α → α → α) (zero : α) (a x : Val α) :
    polyEval addF mulF zero [a] x = a := rfl

-- ============================================================================
-- Absorption: Evaluation at Origin
-- ============================================================================

/-- Non-constant polynomial at origin = origin. -/
theorem polyEval_at_origin (addF mulF : α → α → α) (zero : α)
    (a b : Val α) (rest : List (Val α)) :
    polyEval addF mulF zero (a :: b :: rest) origin = origin := by
  show add addF a (mul mulF origin (polyEval addF mulF zero (b :: rest) origin)) = origin
  simp

-- ============================================================================
-- Contents Closure
-- ============================================================================

/-- Linear: contents coefficients at contents point gives contents. -/
theorem polyEval_contents_linear (addF mulF : α → α → α) (zero : α) (a₀ a₁ v : α) :
    polyEval addF mulF zero [contents a₀, contents a₁] (contents v) =
    contents (addF a₀ (mulF v a₁)) := rfl

/-- Quadratic: contents coefficients at contents point gives contents. -/
theorem polyEval_contents_quad (addF mulF : α → α → α) (zero : α) (a₀ a₁ a₂ v : α) :
    polyEval addF mulF zero [contents a₀, contents a₁, contents a₂] (contents v) =
    contents (addF a₀ (mulF v (addF a₁ (mulF v a₂)))) := rfl

/-- Contents-only polynomial at contents never produces origin. -/
theorem polyEval_contents_ne_origin_linear (addF mulF : α → α → α) (zero : α) (a₀ a₁ v : α) :
    polyEval addF mulF zero [contents a₀, contents a₁] (contents v) ≠ origin := by
  simp [polyEval]

-- ============================================================================
-- Faithful Embedding
-- ============================================================================

/-- Raw polynomial evaluation on α (same algorithm, no wrapper). -/
def polyEvalRaw (addF mulF : α → α → α) (zero : α) : List α → α → α
  | [], _ => zero
  | [a], _ => a
  | a :: b :: rest, x => addF a (mulF x (polyEvalRaw addF mulF zero (b :: rest) x))

/-- Faithful embedding at degree 1: polyEval on contents = contents of polyEvalRaw. -/
theorem polyEval_faithful_linear (addF mulF : α → α → α) (zero : α) (a₀ a₁ v : α) :
    polyEval addF mulF zero [contents a₀, contents a₁] (contents v) =
    contents (polyEvalRaw addF mulF zero [a₀, a₁] v) := rfl

/-- Faithful embedding at degree 2. -/
theorem polyEval_faithful_quad (addF mulF : α → α → α) (zero : α) (a₀ a₁ a₂ v : α) :
    polyEval addF mulF zero [contents a₀, contents a₁, contents a₂] (contents v) =
    contents (polyEvalRaw addF mulF zero [a₀, a₁, a₂] v) := rfl

-- ============================================================================
-- Origin Coefficient Propagation
-- ============================================================================

/-- Origin as leading coefficient: evaluation is origin. -/
theorem origin_head_propagates (addF mulF : α → α → α) (zero : α)
    (b : Val α) (rest : List (Val α)) (x : Val α) :
    polyEval addF mulF zero (origin :: b :: rest) x = origin := by
  show add addF origin (mul mulF x (polyEval addF mulF zero (b :: rest) x)) = origin
  simp

/-- If inner evaluation is origin, outer evaluation is origin. -/
theorem origin_propagates_outward (addF mulF : α → α → α) (zero : α)
    (a b : Val α) (rest : List (Val α)) (x : Val α)
    (h : polyEval addF mulF zero (b :: rest) x = origin) :
    polyEval addF mulF zero (a :: b :: rest) x = origin := by
  show add addF a (mul mulF x (polyEval addF mulF zero (b :: rest) x)) = origin
  rw [h]; simp

-- ============================================================================
-- Polynomial Addition
-- ============================================================================

/-- Coefficient-wise addition of two polynomials. -/
def polyAdd (addF : α → α → α) : List (Val α) → List (Val α) → List (Val α)
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => add addF a b :: polyAdd addF as bs

@[simp] theorem polyAdd_nil_left (addF : α → α → α) (q : List (Val α)) :
    polyAdd addF [] q = q := by cases q <;> rfl

@[simp] theorem polyAdd_nil_right (addF : α → α → α) (p : List (Val α)) :
    polyAdd addF p [] = p := by cases p <;> rfl

/-- Adding contents-coefficient polynomials gives contents coefficients. -/
theorem polyAdd_contents_linear (addF : α → α → α) (a₀ a₁ b₀ b₁ : α) :
    polyAdd addF [contents a₀, contents a₁] [contents b₀, contents b₁] =
    [contents (addF a₀ b₀), contents (addF a₁ b₁)] := rfl

end Val
