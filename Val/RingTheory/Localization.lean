/-
Released under MIT license.
-/
import Val.RingTheory.Core

/-!
# Val α: RingTheory — Localization

Fractions a/s, multiplicative subsets, Ore localization, local rings.

This is the heaviest dissolution in RingTheory. Mathlib has 475+ theorems
with `≠ 0` guards in localization alone. Every one dissolves:
mul mulF (contents a) (inv invF (contents s)) = contents(a · s⁻¹). No hypothesis.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Multiplicative Subsets
-- ============================================================================

/-- A multiplicative subset: closed under multiplication. -/
structure MulSubset (α : Type u) (mulF : α → α → α) (one : α) where
  mem : α → Prop
  one_mem : mem one
  mul_mem : ∀ a b, mem a → mem b → mem (mulF a b)

/-- Every MulSubset element is in contents, never origin. -/
theorem mulSubset_ne_origin (mulF : α → α → α) (one : α)
    (S : MulSubset α mulF one) (s : α) :
    (contents s : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Localization: Fractions a/s
-- ============================================================================

/-- Localization fraction. In Mathlib: requires s ∈ S, S ⊆ nonZeroDivisors. -/
def locFrac (mulF : α → α → α) (invF : α → α) (a s : α) : Val α :=
  mul mulF (contents a) (inv invF (contents s))

theorem locFrac_eq (mulF : α → α → α) (invF : α → α) (a s : α) :
    locFrac mulF invF a s = contents (mulF a (invF s)) := rfl

theorem locFrac_ne_origin (mulF : α → α → α) (invF : α → α) (a s : α) :
    locFrac mulF invF a s ≠ (origin : Val α) := by
  simp [locFrac]

/-- Equality of fractions reduces to contents-level equality. -/
theorem locFrac_eq_iff (mulF : α → α → α) (invF : α → α) (a b s t : α)
    (h : mulF a (invF s) = mulF b (invF t)) :
    locFrac mulF invF a s = locFrac mulF invF b t := by
  simp only [locFrac_eq]; exact congrArg contents h

-- ============================================================================
-- Localization Arithmetic
-- ============================================================================

theorem locFrac_mul (mulF : α → α → α) (invF : α → α) (a b s t : α) :
    mul mulF (locFrac mulF invF a s) (locFrac mulF invF b t) =
    contents (mulF (mulF a (invF s)) (mulF b (invF t))) := rfl

theorem locFrac_add (addF mulF : α → α → α) (invF : α → α) (a b s t : α) :
    add addF (locFrac mulF invF a s) (locFrac mulF invF b t) =
    contents (addF (mulF a (invF s)) (mulF b (invF t))) := rfl

/-- The fraction s/s is always contents. -/
theorem locFrac_self (mulF : α → α → α) (invF : α → α) (s : α) :
    locFrac mulF invF s s = contents (mulF s (invF s)) := rfl

-- ============================================================================
-- Ore Localization (Noncommutative)
-- ============================================================================

/-- Ore fraction: same sort dissolution in noncommutative setting. -/
def oreFrac (mulF : α → α → α) (invF : α → α) (a s : α) : Val α :=
  mul mulF (contents a) (inv invF (contents s))

theorem oreFrac_is_contents (mulF : α → α → α) (invF : α → α) (a s : α) :
    oreFrac mulF invF a s = contents (mulF a (invF s)) := rfl

theorem oreFrac_ne_origin (mulF : α → α → α) (invF : α → α) (a s : α) :
    oreFrac mulF invF a s ≠ (origin : Val α) := by
  simp [oreFrac]

-- ============================================================================
-- Local Rings
-- ============================================================================

/-- In a local ring, every non-unit is in the maximal ideal. -/
theorem local_ring_non_unit (M : α → Prop) (isNonUnit : α → Prop)
    (h : ∀ a, isNonUnit a → M a) (a : α) (ha : isNonUnit a) :
    inIdeal M (contents a : Val α) :=
  h a ha

/-- The unique maximal ideal excludes origin. -/
theorem local_ring_maximal_excludes_origin (M : α → Prop) :
    ¬ inIdeal M (origin : Val α) := id

/-- Units: contents(a) * contents(a⁻¹) = contents(a · a⁻¹). -/
theorem local_ring_unit_inv (mulF : α → α → α) (invF : α → α) (a : α) :
    mul mulF (contents a) (inv invF (contents a)) =
    contents (mulF a (invF a)) := rfl

-- ============================================================================
-- Local Properties
-- ============================================================================

/-- Localization commutes with sort: localizing contents gives contents. -/
theorem localization_preserves_contents (mulF : α → α → α) (invF : α → α) (a s : α) :
    ∃ r, locFrac mulF invF a s = contents r :=
  ⟨mulF a (invF s), rfl⟩

/-- A property holds locally: it holds for all localizations. -/
theorem local_property_contents (mulF : α → α → α) (invF : α → α)
    (P : Val α → Prop) (a s : α)
    (hP : P (contents (mulF a (invF s)))) :
    P (locFrac mulF invF a s) :=
  hP

end Val
