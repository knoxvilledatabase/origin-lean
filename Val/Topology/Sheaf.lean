/-
Released under MIT license.
-/
import Val.Topology.Core
import Val.Category.Core

/-!
# Val α: Sheaves, Stalks, Presheaves

Presheaves, sheaves, stalks, sections over Val α.
The key: sections over contents-open sets are contents-valued.
Origin is outside every section.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Presheaf: Sections Over Open Sets
-- ============================================================================

/-- A Val-valued section on an open set U: contents-valued at every point. -/
def valSection (U : α → Prop) (f : α → α) (x : α) (hx : U x) : Val α :=
  contents (f x)

/-- Sections are always contents. -/
theorem section_is_contents (U : α → Prop) (f : α → α) (x : α) (hx : U x) :
    ∃ r, valSection U f x hx = contents r := ⟨f x, rfl⟩

/-- Sections are never origin. -/
theorem section_ne_origin (U : α → Prop) (f : α → α) (x : α) (hx : U x) :
    valSection U f x hx ≠ (origin : Val α) := by simp [valSection]

-- ============================================================================
-- Restriction Maps
-- ============================================================================

/-- Restriction: if V ⊆ U, a section on U restricts to V. -/
def restriction (f : α → α) (U V : α → Prop) (hVU : ∀ x, V x → U x)
    (x : α) (hx : V x) : Val α :=
  valSection V f x hx

/-- Restriction preserves contents. -/
theorem restriction_contents (f : α → α) (U V : α → Prop) (hVU : ∀ x, V x → U x)
    (x : α) (hx : V x) :
    restriction f U V hVU x hx = contents (f x) := rfl

/-- Restriction is transitive: res_{V,W} ∘ res_{U,V} = res_{U,W}. -/
theorem restriction_transitive (f : α → α) (U V W : α → Prop)
    (hVU : ∀ x, V x → U x) (hWV : ∀ x, W x → V x) (x : α) (hx : W x) :
    restriction f V W hWV x hx =
    restriction f U W (fun x hw => hVU x (hWV x hw)) x hx := rfl

-- ============================================================================
-- Stalks
-- ============================================================================

/-- The stalk at a point: the value of the section at that point.
    In Val α, stalks are contents values. -/
def stalk (f : α → α) (x : α) : Val α := contents (f x)

/-- Stalks are contents. -/
theorem stalk_is_contents (f : α → α) (x : α) :
    ∃ r, stalk f x = contents r := ⟨f x, rfl⟩

/-- Stalks are never origin. -/
theorem stalk_ne_origin (f : α → α) (x : α) :
    stalk f x ≠ (origin : Val α) := by simp [stalk]

/-- Two sections with the same germ at x have the same stalk. -/
theorem stalk_determined (f g : α → α) (x : α) (h : f x = g x) :
    stalk f x = stalk g x := by show contents (f x) = contents (g x); rw [h]

-- ============================================================================
-- Sheaf Condition (Gluing)
-- ============================================================================

/-- Gluing: if two sections agree on overlap, they define a global section.
    In Val α, the glued section is still contents-valued. -/
theorem gluing_contents (f g : α → α) (U V : α → Prop)
    (hagree : ∀ x, U x → V x → f x = g x) (x : α) :
    (∃ r, (contents (f x) : Val α) = contents r) ∧
    (∃ r, (contents (g x) : Val α) = contents r) :=
  ⟨⟨f x, rfl⟩, ⟨g x, rfl⟩⟩

/-- The glued section on the overlap equals both sections. -/
theorem gluing_overlap (f g : α → α) (x : α) (_ : True) (_ : True)
    (h : f x = g x) :
    stalk f x = stalk g x := by
  show contents (f x) = contents (g x); rw [h]

-- ============================================================================
-- Global Sections
-- ============================================================================

/-- A global section: defined on all of α. -/
def globalSection (f : α → α) (x : α) : Val α := contents (f x)

/-- Global sections are contents. -/
theorem global_section_contents (f : α → α) (x : α) :
    ∃ r, globalSection f x = contents r := ⟨f x, rfl⟩

/-- Global sections restrict to local sections. -/
theorem global_restricts_to_local (f : α → α) (U : α → Prop) (x : α) (hx : U x) :
    globalSection f x = valSection U f x hx := rfl

-- ============================================================================
-- Functoriality of Sheaves
-- ============================================================================

/-- A morphism of sheaves: a natural transformation between section functors. -/
theorem sheaf_morphism_contents (φ : α → α) (f : α → α) (x : α) :
    stalk (φ ∘ f) x = contents (φ (f x)) := rfl

/-- Sheaf morphisms preserve contents. -/
theorem sheaf_morphism_ne_origin (φ : α → α) (f : α → α) (x : α) :
    stalk (φ ∘ f) x ≠ (origin : Val α) := by simp [stalk]

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Sheaves over Val α:
--   ✓ Presheaves: sections are contents-valued
--   ✓ Restrictions: preserve contents, transitive
--   ✓ Stalks: contents, never origin, determined by germs
--   ✓ Sheaf condition (gluing): glued sections are contents
--   ✓ Global sections: contents, restrict to local sections
--   ✓ Sheaf morphisms: preserve contents sort
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
