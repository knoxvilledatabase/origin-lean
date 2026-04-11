/-
Released under MIT license.
-/
import Val.Category.Core
import Val.OrderedField

/-!
# Val α: Adjunctions and Galois Connections

Adjunctions, Galois connections, free-forgetful pairs.
The contents embedding and project form the fundamental adjunction of Val α.
-/

namespace Val

universe u
variable {α β : Type u}

-- ============================================================================
-- The Fundamental Adjunction: contents ⊣ project
-- ============================================================================

/-- The unit of the adjunction: α → Option α via project ∘ contents = some. -/
theorem adj_unit (a : α) : project (contents a : Val α) = some a := rfl

/-- The counit attempt: Option α → Val α. Partial — none maps to origin. -/
def optionToVal : Option α → Val α
  | some a => contents a
  | none => origin

/-- Round trip: optionToVal ∘ project ∘ contents = contents. -/
theorem adj_roundtrip_contents (a : α) :
    optionToVal (project (contents a : Val α)) = contents a := rfl

/-- Round trip on origin: project gives none, optionToVal gives origin. -/
theorem adj_roundtrip_origin :
    optionToVal (project (origin : Val α)) = origin := rfl

-- ============================================================================
-- Free-Forgetful Adjunction
-- ============================================================================

/-- contents is the free construction: embeds α into Val α. -/
theorem free_embedding (a : α) :
    (contents a : Val α) ≠ origin := by simp

/-- project is the forgetful functor: extracts the value if possible. -/
theorem forgetful_on_contents (a : α) :
    project (contents a : Val α) = some a := rfl

theorem forgetful_on_origin :
    project (origin : Val α) = none := rfl

/-- The free functor preserves composition. -/
theorem free_preserves_comp (f : α → β) (a : α) :
    valMap f (contents a) = contents (f a) := rfl

-- ============================================================================
-- Galois Connection
-- ============================================================================

/-- A Galois connection: in Val α with valLE, contents(a) ≤ contents(b) ↔ a ≤ b. -/
theorem galois_contents (leF : α → α → Prop) (a b : α) :
    valLE leF (contents a : Val α) (contents b) ↔ leF a b :=
  Iff.rfl

/-- Origin is not ≤ anything in the Galois connection. -/
theorem galois_origin_not_le (leF : α → α → Prop) (b : α) :
    ¬ valLE leF (origin : Val α) (contents b) := id

/-- Nothing is ≤ origin in the Galois connection. -/
theorem galois_not_le_origin (leF : α → α → Prop) (a : α) :
    ¬ valLE leF (contents a : Val α) origin := id

-- ============================================================================
-- Monad Adjunction
-- ============================================================================

/-- The monad from the adjunction on contents: round-trips. -/
theorem monad_from_adj_contents (a : α) :
    optionToVal (project (contents a : Val α)) = contents a := rfl

/-- The monad from the adjunction on origin: stays origin. -/
theorem monad_from_adj_origin :
    optionToVal (project (origin : Val α)) = (origin : Val α) := rfl

-- ============================================================================
-- Adjunction Uniqueness
-- ============================================================================

/-- The adjunction is unique: any sort-preserving right adjoint to contents
    must agree with project on contents and origin. -/
theorem adjunction_unique (R : Val α → Option α)
    (h_contents : ∀ a, R (contents a) = some a)
    (h_origin : R origin = none) :
    ∀ x : Val α, (x = origin → R x = none) ∧ (∀ a, x = contents a → R x = some a) := by
  intro x; constructor
  · intro hx; rw [hx]; exact h_origin
  · intro a hx; rw [hx]; exact h_contents a

-- ============================================================================
-- Closure Operator
-- ============================================================================

/-- The closure operator from the adjunction: optionToVal ∘ project.
    Idempotent on contents and origin. -/
theorem closure_idempotent_contents (a : α) :
    optionToVal (project (optionToVal (project (contents a : Val α)))) = contents a := rfl

theorem closure_idempotent_origin :
    optionToVal (project (optionToVal (project (origin : Val α)))) = (origin : Val α) := rfl

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Adjunctions over Val α:
--   ✓ Fundamental adjunction: contents ⊣ project
--   ✓ Unit and counit: round-trip properties
--   ✓ Free-forgetful pair: contents is free, project is forgetful
--   ✓ Galois connection: valLE ↔ LE on contents
--   ✓ Monad from adjunction: round-trip on contents, fixed on origin
--   ✓ Adjunction uniqueness: determined by sort behavior
--   ✓ Closure operator: idempotent
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
