/-
Released under MIT license.
-/
import Val.Topology.Core
import Val.Category.Core

/-!
# Val α: Continuous Maps and Homeomorphisms

Continuity, open maps, closed maps, homeomorphisms, embeddings.
Sort-preserving maps are automatically continuous in the sort topology.
-/

namespace Val

universe u
variable {α β : Type u}

-- ============================================================================
-- Continuous Maps
-- ============================================================================

/-- A map f : Val α → Val β is sort-continuous if it preserves sort structure. -/
def sortContinuous (f : Val α → Val β) : Prop :=
  f origin = origin ∧
  ((∀ a : α, ∃ b : β, f (contents a) = contents b) ∨
   (∀ a : α, f (contents a) = origin))

/-- valMap is sort-continuous (strong form: contents to contents). -/
theorem valMap_sort_continuous (f : α → β) :
    valMap f origin = (origin : Val β) ∧
    ∀ a : α, ∃ b : β, valMap f (contents a) = contents b :=
  ⟨rfl, fun a => ⟨f a, rfl⟩⟩

-- ============================================================================
-- Open Maps
-- ============================================================================

/-- A map is sort-open if it maps contents to contents. -/
def isSortOpen (f : Val α → Val β) : Prop :=
  ∀ a : α, ∃ b : β, f (contents a) = contents b

/-- valMap is sort-open. -/
theorem valMap_is_sort_open (f : α → β) : isSortOpen (valMap f) :=
  fun a => ⟨f a, rfl⟩

-- ============================================================================
-- Closed Maps
-- ============================================================================

/-- A map is sort-closed if it maps origin to origin. -/
def isSortClosed (f : Val α → Val β) : Prop :=
  f origin = origin

/-- valMap is sort-closed. -/
theorem valMap_is_sort_closed (f : α → β) : isSortClosed (valMap f) := rfl

-- ============================================================================
-- Homeomorphism
-- ============================================================================

/-- Two Val spaces are sort-homeomorphic if there's a bijective sort-preserving map. -/
structure SortHomeo (α β : Type u) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- A SortHomeo lifts to a homeomorphism on Val. -/
def liftHomeo (h : SortHomeo α β) : Val α → Val β := valMap h.toFun

/-- The inverse of a lifted homeomorphism. -/
def liftHomeoInv (h : SortHomeo α β) : Val β → Val α := valMap h.invFun

/-- The lifted homeomorphism is a left inverse. -/
theorem liftHomeo_left_inv (h : SortHomeo α β) (x : Val α) :
    liftHomeoInv h (liftHomeo h x) = x := by
  cases x with
  | origin => rfl
  | container a => show container (h.invFun (h.toFun a)) = container a; rw [h.left_inv]
  | contents a => show contents (h.invFun (h.toFun a)) = contents a; rw [h.left_inv]

/-- The lifted homeomorphism is a right inverse. -/
theorem liftHomeo_right_inv (h : SortHomeo α β) (y : Val β) :
    liftHomeo h (liftHomeoInv h y) = y := by
  cases y with
  | origin => rfl
  | container b => show container (h.toFun (h.invFun b)) = container b; rw [h.right_inv]
  | contents b => show contents (h.toFun (h.invFun b)) = contents b; rw [h.right_inv]

-- ============================================================================
-- Embeddings
-- ============================================================================

/-- Contents embedding is injective. -/
theorem contents_embedding_injective (a b : α) (h : (contents a : Val α) = contents b) :
    a = b := Val.contents_injective a b h

/-- The contents embedding preserves distinctness. -/
theorem contents_embedding_faithful (a b : α) (h : a ≠ b) :
    (contents a : Val α) ≠ contents b := by
  intro heq; exact h (Val.contents_injective a b heq)

-- ============================================================================
-- Quotient Maps
-- ============================================================================

/-- A quotient map on α lifts to Val α. -/
def liftQuotient (proj : α → β) : Val α → Val β := valMap proj

/-- Quotient maps preserve sort. -/
theorem quotient_preserves_sort' (proj : α → β) (a : α) :
    liftQuotient proj (contents a) = contents (proj a) := rfl

/-- Quotient maps send origin to origin. -/
theorem quotient_origin (proj : α → β) :
    liftQuotient proj (origin : Val α) = (origin : Val β) := rfl

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Continuous maps over Val α:
--   ✓ Sort-continuous maps: preserve sort structure
--   ✓ valMap is sort-continuous, sort-open, sort-closed
--   ✓ Homeomorphisms: bijective sort-preserving maps lift
--   ✓ Left and right inverse for lifted homeomorphisms
--   ✓ Embeddings: contents is injective and faithful
--   ✓ Quotient maps: sort-preserving
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
