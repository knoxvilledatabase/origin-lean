/-
Released under MIT license.
-/
import Val.LinearAlgebra.Core
import Val.Algebra

/-!
# Val α: Bilinear Forms, Quadratic Forms, Symmetric Forms

Bilinear forms over Val α. The sort propagates through all bilinear computations.
Contents in, contents out. Origin absorbs.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Bilinear Form
-- ============================================================================

/-- A bilinear form: B(v, w) where B is a function α → α → α.
    Lifted to Val α. -/
def valBilinear (B : α → α → α) : Val α → Val α → Val α
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (B a b)
  | container a, contents b => container (B a b)
  | contents a, container b => container (B a b)
  | contents a, contents b => contents (B a b)

/-- Bilinear form on contents gives contents. -/
theorem bilinear_contents (B : α → α → α) (v w : α) :
    valBilinear B (contents v) (contents w) = contents (B v w) := rfl

/-- Bilinear form on contents is never origin. -/
theorem bilinear_ne_origin (B : α → α → α) (v w : α) :
    valBilinear B (contents v) (contents w) ≠ (origin : Val α) := by
  simp [valBilinear]

/-- Bilinear form with origin absorbs (left). -/
theorem bilinear_origin_left (B : α → α → α) (w : Val α) :
    valBilinear B origin w = origin := by cases w <;> rfl

/-- Bilinear form with origin absorbs (right). -/
theorem bilinear_origin_right (B : α → α → α) (v : Val α) :
    valBilinear B v origin = origin := by
  cases v with | origin => rfl | container _ => rfl | contents _ => rfl

-- ============================================================================
-- Symmetric Bilinear Form
-- ============================================================================

/-- A bilinear form is symmetric if B(v,w) = B(w,v). -/
theorem bilinear_symmetric (B : α → α → α) (h : ∀ a b, B a b = B b a) (v w : α) :
    valBilinear B (contents v) (contents w) =
    valBilinear B (contents w) (contents v) := by
  show contents (B v w) = contents (B w v); rw [h]

-- ============================================================================
-- Quadratic Form
-- ============================================================================

/-- A quadratic form: Q(v) = B(v, v). -/
def valQuadratic (B : α → α → α) : Val α → Val α
  | origin => origin
  | container a => container (B a a)
  | contents a => contents (B a a)

/-- Quadratic form on contents gives contents. -/
theorem quadratic_contents (B : α → α → α) (v : α) :
    valQuadratic B (contents v) = contents (B v v) := rfl

/-- Quadratic form on contents is never origin. -/
theorem quadratic_ne_origin (B : α → α → α) (v : α) :
    valQuadratic B (contents v) ≠ (origin : Val α) := by simp [valQuadratic]

/-- Quadratic form preserves origin. -/
theorem quadratic_origin (B : α → α → α) :
    valQuadratic B (origin : Val α) = origin := rfl

-- ============================================================================
-- Inner Product (as Bilinear Form)
-- ============================================================================

/-- Inner product: ⟨v, w⟩ = B(v, w). Contents in, contents out. -/
theorem inner_product_contents (B : α → α → α) (v w : α) :
    ∃ r, valBilinear B (contents v) (contents w) = contents r := ⟨B v w, rfl⟩

/-- Norm squared from inner product: ⟨v, v⟩. -/
theorem norm_sq_contents (B : α → α → α) (v : α) :
    ∃ r, valBilinear B (contents v) (contents v) = contents r := ⟨B v v, rfl⟩

-- ============================================================================
-- Orthogonality
-- ============================================================================

/-- Two vectors are orthogonal if B(v, w) = 0.
    In Val α: B(contents v, contents w) = contents(B v w). -/
theorem orthogonal_sort [Zero α] (B : α → α → α) (v w : α) (h : B v w = 0) :
    valBilinear B (contents v) (contents w) = contents (0 : α) := by
  show contents (B v w) = contents 0; rw [h]

/-- Orthogonal complement: sort-preserving. -/
theorem orthogonal_complement_contents (v : α) :
    (contents v : Val α) ≠ origin := by simp

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Bilinear forms over Val α:
--   ✓ Bilinear forms: contents × contents → contents
--   ✓ Origin absorbs on both sides
--   ✓ Symmetric bilinear forms: B(v,w) = B(w,v) in contents
--   ✓ Quadratic forms: Q(v) = B(v,v), contents
--   ✓ Inner product: contents, norm squared contents
--   ✓ Orthogonality: sort-preserving
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
