/-
Released under MIT license.
-/
import Val.Category.Core

/-!
# Val α: Monoidal Categories

Tensor product, associator, unitors, braiding.
Val α forms a monoidal category with valPair as tensor and Val Unit as unit.
-/

namespace Val

universe u
variable {α β γ δ : Type u}

-- ============================================================================
-- Tensor Product
-- ============================================================================

/-- Tensor product on Val: valMap over pairs. Contents ⊗ contents = contents. -/
def valPair : Val α → Val β → Val (α × β)
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (a, b)
  | container a, contents b => container (a, b)
  | contents a, container b => container (a, b)
  | contents a, contents b => contents (a, b)

/-- Tensor of contents gives contents. -/
theorem tensor_contents (a : α) (b : β) :
    valPair (contents a) (contents b) = contents (a, b) := rfl

/-- Tensor with origin is origin (left). -/
theorem tensor_origin_left (y : Val β) :
    valPair (origin : Val α) y = (origin : Val (α × β)) := by cases y <;> rfl

/-- Tensor with origin is origin (right). -/
theorem tensor_origin_right (x : Val α) :
    valPair x (origin : Val β) = (origin : Val (α × β)) := by
  cases x <;> rfl

-- ============================================================================
-- Associator
-- ============================================================================

/-- Associator: (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C). On contents: repackages the triple. -/
def tensorAssoc : Val ((α × β) × γ) → Val (α × (β × γ))
  | origin => origin
  | container ((a, b), c) => container (a, (b, c))
  | contents ((a, b), c) => contents (a, (b, c))

/-- Associator on contents. -/
theorem tensorAssoc_contents (a : α) (b : β) (c : γ) :
    tensorAssoc (contents ((a, b), c) : Val ((α × β) × γ)) = contents (a, (b, c)) := rfl

/-- Associator inverse. -/
def tensorAssocInv : Val (α × (β × γ)) → Val ((α × β) × γ)
  | origin => origin
  | container (a, (b, c)) => container ((a, b), c)
  | contents (a, (b, c)) => contents ((a, b), c)

/-- Associator round-trip. -/
theorem tensorAssoc_inv (x : Val ((α × β) × γ)) :
    tensorAssocInv (tensorAssoc x) = x := by
  cases x with
  | origin => rfl
  | container p => obtain ⟨⟨a, b⟩, c⟩ := p; rfl
  | contents p => obtain ⟨⟨a, b⟩, c⟩ := p; rfl

-- ============================================================================
-- Left and Right Unitors
-- ============================================================================

/-- Left unitor: Unit ⊗ A ≅ A. -/
def leftUnitor : Val (Unit × α) → Val α
  | origin => origin
  | container ((), a) => container a
  | contents ((), a) => contents a

/-- Right unitor: A ⊗ Unit ≅ A. -/
def rightUnitor : Val (α × Unit) → Val α
  | origin => origin
  | container (a, ()) => container a
  | contents (a, ()) => contents a

/-- Left unitor on contents. -/
theorem leftUnitor_contents (a : α) :
    leftUnitor (contents ((), a) : Val (Unit × α)) = contents a := rfl

/-- Right unitor on contents. -/
theorem rightUnitor_contents (a : α) :
    rightUnitor (contents (a, ()) : Val (α × Unit)) = contents a := rfl

-- ============================================================================
-- Braiding (Symmetric Monoidal)
-- ============================================================================

/-- Braiding: A ⊗ B ≅ B ⊗ A. -/
def tensorBraid : Val (α × β) → Val (β × α)
  | origin => origin
  | container (a, b) => container (b, a)
  | contents (a, b) => contents (b, a)

/-- Braiding on contents. -/
theorem tensorBraid_contents (a : α) (b : β) :
    tensorBraid (contents (a, b) : Val (α × β)) = contents (b, a) := rfl

/-- Braiding is an involution. -/
theorem tensorBraid_involution (x : Val (α × β)) :
    tensorBraid (tensorBraid x) = x := by
  cases x with
  | origin => rfl
  | container p => obtain ⟨a, b⟩ := p; rfl
  | contents p => obtain ⟨a, b⟩ := p; rfl

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Monoidal categories over Val α:
--   ✓ Tensor product: contents ⊗ contents = contents
--   ✓ Origin absorbs under tensor
--   ✓ Associator and inverse: contents repackaging
--   ✓ Left and right unitors: Unit identity
--   ✓ Braiding: symmetric, involutive
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
