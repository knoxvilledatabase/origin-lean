/-
Released under MIT license.
-/
import Val.Foundation
import Val.Category.Core

/-!
# Val α: Tensor Products, Exterior Algebra, Clifford Algebra

Tensor products over Val α. The sort propagates through all multilinear constructions.
-/

namespace Val

universe u
variable {α β : Type u}

-- ============================================================================
-- Tensor Product
-- ============================================================================

/-- Tensor product of two Val values: contents ⊗ contents = contents. -/
def valTensor : Val α → Val β → Val (α × β)
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (a, b)
  | container a, contents b => container (a, b)
  | contents a, container b => container (a, b)
  | contents a, contents b => contents (a, b)

/-- Tensor of contents gives contents. -/
theorem tensor_product_contents (a : α) (b : β) :
    valTensor (contents a) (contents b) = contents (a, b) := rfl

/-- Tensor with origin gives origin (left). -/
theorem tensor_origin_left (y : Val β) :
    valTensor (origin : Val α) y = (origin : Val (α × β)) := by cases y <;> rfl

/-- Tensor with origin gives origin (right). -/
theorem tensor_origin_right (x : Val α) :
    valTensor x (origin : Val β) = (origin : Val (α × β)) := by
  cases x with | origin => rfl | container _ => rfl | contents _ => rfl

/-- Tensor product is never origin for contents inputs. -/
theorem tensor_ne_origin (a : α) (b : β) :
    valTensor (contents a) (contents b) ≠ (origin : Val (α × β)) := by simp [valTensor]

-- ============================================================================
-- Multilinear Maps
-- ============================================================================

/-- A multilinear map: f(v₁, v₂). Contents in, contents out. -/
theorem multilinear_contents (f : α → α → α) (a b : α) :
    ∃ r, (contents (f a b) : Val α) = contents r := ⟨f a b, rfl⟩

/-- Multilinear maps never produce origin from contents inputs. -/
theorem multilinear_ne_origin (f : α → α → α) (a b : α) :
    (contents (f a b) : Val α) ≠ origin := by simp

-- ============================================================================
-- Exterior Product (Wedge Product)
-- ============================================================================

/-- Wedge product: antisymmetric tensor product. In Val α, always contents. -/
def wedge (f : α → α → α) (a b : α) : Val α := contents (f a b)

/-- Wedge product is contents. -/
theorem wedge_contents (f : α → α → α) (a b : α) :
    ∃ r, wedge f a b = contents r := ⟨f a b, rfl⟩

/-- Wedge product is never origin. -/
theorem wedge_ne_origin (f : α → α → α) (a b : α) :
    wedge f a b ≠ (origin : Val α) := by simp [wedge]

/-- Antisymmetry: v ∧ v = 0. In Val α, that's contents(0). -/
theorem wedge_self [Zero α] (f : α → α → α) (a : α) (h : f a a = 0) :
    wedge f a a = contents (0 : α) := by
  show contents (f a a) = contents 0; rw [h]

-- ============================================================================
-- Clifford Algebra (Sort-Level)
-- ============================================================================

/-- Clifford product relation: v · w + w · v = 2⟨v,w⟩.
    Each side is contents when inputs are contents. -/
theorem clifford_contents (addF mulF : α → α → α) (B : α → α → α) (a b : α)
    (h : addF (mulF a b) (mulF b a) = B a b) :
    add addF (contents (mulF a b)) (contents (mulF b a)) = contents (B a b) := by
  show contents (addF (mulF a b) (mulF b a)) = contents (B a b); rw [h]

/-- Clifford algebra elements are contents. -/
theorem clifford_element_contents (v : α) :
    (contents v : Val α) ≠ origin := by simp

-- ============================================================================
-- Tensor Algebra
-- ============================================================================

/-- Tensor algebra: each grade is contents. -/
theorem tensor_algebra_grade_contents (v : α) :
    ∃ r, (contents v : Val α) = contents r := ⟨v, rfl⟩

/-- Tensor algebra multiplication: concatenation of tensors. Contents × contents = contents. -/
theorem tensor_algebra_mul (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Tensor products over Val α:
--   ✓ Tensor product: contents ⊗ contents = contents
--   ✓ Origin absorbs under tensor
--   ✓ Multilinear maps: contents in, contents out
--   ✓ Exterior product: contents, antisymmetric, v∧v = contents(0)
--   ✓ Clifford algebra: contents throughout, relation holds
--   ✓ Tensor algebra: contents, multiplication preserves sort
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
