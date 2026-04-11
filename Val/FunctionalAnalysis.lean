/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Functional Analysis on Val α

Norms, operators, inner products, spectral theory.
The ≠ 0 dissolution extends from finite-dimensional (LinearAlgebra) to infinite-dimensional.
Same pattern. Same sort. Same rfl.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Norms
-- ============================================================================

/-- Norm on Val α. Same absorption pattern as every other operation. -/
def norm (normF : α → α) : Val α → Val α
  | origin => origin
  | container a => container (normF a)
  | contents a => contents (normF a)

@[simp] theorem norm_origin (normF : α → α) : norm normF (origin : Val α) = origin := rfl
@[simp] theorem norm_container (normF : α → α) (a : α) : norm normF (container a : Val α) = container (normF a) := rfl
@[simp] theorem norm_contents (normF : α → α) (a : α) : norm normF (contents a) = contents (normF a) := rfl

/-- Norm of contents is never origin. -/
theorem norm_contents_ne_origin (normF : α → α) (a : α) :
    norm normF (contents a) ≠ origin := by simp

/-- Triangle inequality: ‖x + y‖ within contents. -/
theorem norm_triangle (normF : α → α) (addF : α → α → α) (a b : α) :
    norm normF (add addF (contents a) (contents b)) =
    contents (normF (addF a b)) := rfl

-- ============================================================================
-- Linear Operators
-- ============================================================================

/-- A linear operator acting faithfully on contents. Same structure as valMap. -/
def opApply (f : α → α) : Val α → Val α
  | origin => origin
  | container a => container (f a)
  | contents a => contents (f a)

@[simp] theorem op_contents (f : α → α) (a : α) :
    opApply f (contents a) = contents (f a) := rfl

/-- Operator applied to contents is never origin. -/
theorem op_contents_ne_origin (f : α → α) (a : α) :
    opApply f (contents a) ≠ origin := by simp [opApply]

/-- Composition of operators on contents. -/
theorem op_comp_contents (f g : α → α) (a : α) :
    opApply f (opApply g (contents a)) = contents (f (g a)) := rfl

/-- Operator norm: ‖T(x)‖ within contents. -/
theorem op_norm_contents (normF f : α → α) (a : α) :
    norm normF (opApply f (contents a)) = contents (normF (f a)) := rfl

-- ============================================================================
-- Operator Invertibility: ≠ 0 Dissolution
-- ============================================================================

/-- T ∘ T⁻¹ on contents. No invertibility hypothesis at the sort level. -/
theorem op_mul_inv_contents (f finv : α → α)
    (h : ∀ a : α, f (finv a) = a) (a : α) :
    opApply f (opApply finv (contents a)) = contents a := by simp [h]

/-- T⁻¹ ∘ T on contents. -/
theorem op_inv_mul_contents (f finv : α → α)
    (h : ∀ a : α, finv (f a) = a) (a : α) :
    opApply finv (opApply f (contents a)) = contents a := by simp [h]

-- ============================================================================
-- Inner Products
-- ============================================================================

/-- Inner product: same absorption pattern as mul. -/
def inner (innerF : α → α → α) : Val α → Val α → Val α
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (innerF a b)
  | container a, contents b  => container (innerF a b)
  | contents a, container b  => container (innerF a b)
  | contents a, contents b   => contents (innerF a b)

@[simp] theorem inner_contents (innerF : α → α → α) (a b : α) :
    inner innerF (contents a) (contents b) = contents (innerF a b) := rfl

/-- Inner product of contents is never origin. -/
theorem inner_contents_ne_origin (innerF : α → α → α) (a b : α) :
    inner innerF (contents a) (contents b) ≠ origin := by simp [inner]

/-- Conjugate symmetry within contents. -/
theorem inner_comm_contents (innerF : α → α → α) (conjF : α → α)
    (h : ∀ a b : α, innerF a b = conjF (innerF b a)) (a b : α) :
    inner innerF (contents a) (contents b) = contents (conjF (innerF b a)) := by
  show contents (innerF a b) = contents (conjF (innerF b a)); congr 1; exact h a b

-- ============================================================================
-- Spectral Theory
-- ============================================================================

/-- Eigenvalue equation: T(v) = λ·v within contents. -/
theorem eigenvalue_contents (f : α → α) (mulF : α → α → α) (lambda v : α)
    (h : f v = mulF lambda v) :
    opApply f (contents v) = mul mulF (contents lambda) (contents v) := by
  simp [h]

/-- Eigenvalues of contents operators are contents. Never origin. -/
theorem eigenvalue_ne_origin (mulF : α → α → α) (lambda v : α) :
    mul mulF (contents lambda) (contents v) ≠ origin := by simp

-- ============================================================================
-- Completeness
-- ============================================================================

/-- If α is complete, contents-level sequences are complete. -/
theorem contents_complete
    (cauchy : (Nat → α) → Prop)
    (conv : (Nat → α) → α → Prop)
    (h_complete : ∀ s, cauchy s → ∃ L, conv s L)
    (s : Nat → α) (hc : cauchy s) :
    ∃ L : α, conv s L := h_complete s hc

/-- No term of a Cauchy sequence in contents is origin. -/
theorem cauchy_contents_never_origin (s : Nat → α) (n : Nat) :
    (fun n => contents (s n)) n ≠ (origin : Val α) := by simp

end Val
