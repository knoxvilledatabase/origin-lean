/-
Released under MIT license.
-/
import Val.RingTheory.Core
import Val.Category.Core

/-!
# Val α: Algebraic Geometry

Spec as topological space, structure sheaf, affine schemes, scheme morphisms,
local rings, stalks. The `s ≠ 0` dissolution in localization cascades through
scheme theory. Origin is outside every prime ideal, every stalk, every section.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Spec: Prime Ideals as Points
-- ============================================================================

/-- A point of Spec: a prime ideal predicate on α with the prime property. -/
structure SpecPoint (α : Type u) where
  ideal : α → Prop
  prime : ∀ (mulF : α → α → α) (a b : α), ideal (mulF a b) → ideal a ∨ ideal b

/-- Origin is outside every Spec point. -/
theorem spec_point_excludes_origin (p : SpecPoint α) :
    ¬ inIdeal p.ideal (origin : Val α) := id

/-- Container is outside every Spec point. -/
theorem spec_point_excludes_container (p : SpecPoint α) (c : α) :
    ¬ inIdeal p.ideal (container c : Val α) := id

-- ============================================================================
-- Basic Open Sets: D(f)
-- ============================================================================

/-- D(f): the set of primes not containing f. -/
def basicOpen (f : α) (P : α → Prop) : Prop := ¬ P f

/-- D(f·g) ⊇ D(f) ∩ D(g): if f ∉ P and g ∉ P, then fg ∉ P (for prime P). -/
theorem basicOpen_mul_of_both (mulF : α → α → α) (f g : α) (P : α → Prop)
    (hP : ∀ a b, P (mulF a b) → P a ∨ P b)
    (hf : basicOpen f P) (hg : basicOpen g P) :
    basicOpen (mulF f g) P :=
  fun hab => (hP f g hab).elim hf hg

-- ============================================================================
-- Structure Sheaf: Sections Are Contents-Valued
-- ============================================================================

/-- Every section is contents-valued. By construction. -/
theorem section_is_contents (s : (α → Prop) → α) (P : α → Prop) :
    ∃ r, (contents (s P) : Val α) = contents r := ⟨s P, rfl⟩

/-- Sections are never origin. -/
theorem section_ne_origin (s : (α → Prop) → α) (P : α → Prop) :
    (contents (s P) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Affine Schemes
-- ============================================================================

/-- Ring operations on global sections stay in contents. -/
theorem global_sections_mul (mulF : α → α → α) (r s : α) :
    mul mulF (contents r) (contents s) = contents (mulF r s) := rfl

theorem global_sections_add (addF : α → α → α) (r s : α) :
    add addF (contents r) (contents s) = contents (addF r s) := rfl

-- ============================================================================
-- Scheme Morphisms
-- ============================================================================

/-- Scheme morphisms send contents to contents via valMap. -/
theorem scheme_morphism_contents (f : α → α) (a : α) :
    valMap f (contents a) = contents (f a) := rfl

/-- Scheme morphisms never send contents to origin. -/
theorem scheme_morphism_ne_origin (f : α → α) (a : α) :
    valMap f (contents a) ≠ (origin : Val α) := by intro h; cases h

/-- Composition of scheme morphisms. -/
theorem scheme_morphism_comp (f g : α → α) :
    valMap (g ∘ f) = valMap g ∘ valMap f := valMap_comp f g

-- ============================================================================
-- Local Rings: Localization at Primes
-- ============================================================================

/-- Local ring element a/s: always contents. No s ≠ 0 sort-level hypothesis. -/
theorem local_ring_element (mulF : α → α → α) (invF : α → α)
    (P : α → Prop) (a s : α) (_ : ¬ P s) :
    ∃ r, mul mulF (contents a) (inv invF (contents s)) = contents r :=
  ⟨mulF a (invF s), rfl⟩

/-- Addition of fractions stays in contents. -/
theorem local_ring_add (mulF addF : α → α → α) (invF : α → α) (a b s t : α) :
    ∃ r, add addF (mul mulF (contents a) (inv invF (contents s)))
                  (mul mulF (contents b) (inv invF (contents t))) = contents r :=
  ⟨addF (mulF a (invF s)) (mulF b (invF t)), rfl⟩

-- ============================================================================
-- Stalks
-- ============================================================================

/-- Stalk operations: multiplication stays in contents. -/
theorem stalk_mul (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

/-- The stalk is never origin. -/
theorem stalk_ne_origin (a : α) :
    (contents a : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Residue Field
-- ============================================================================

/-- Residue field element: quotient map sends contents to contents. -/
theorem residue_field_contents (proj : α → α) (a : α) :
    quotientMap proj (contents a) = contents (proj a) := rfl

/-- Residue field element is never origin (scheme-level). -/
theorem scheme_residue_ne_origin (proj : α → α) (a : α) :
    quotientMap proj (contents a) ≠ origin := by simp [quotientMap]

-- ============================================================================
-- Separatedness
-- ============================================================================

/-- Distinct contents values are distinguishable. -/
theorem separated_diagonal (a b : α) (h : a ≠ b) :
    (contents a : Val α) ≠ contents b :=
  fun heq => h (contents_injective a b heq)

end Val
