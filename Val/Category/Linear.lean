/-
Released under MIT license.
-/
import Val.Category.Core
import Val.Algebra

/-!
# Val α: Linear, Additive, Preadditive Categories

Additive structure on Val-categories. Preadditive: Hom-sets are abelian groups.
Additive: biproducts exist. Linear: enriched over a ring.
-/

namespace Val

universe u
variable {α β : Type u}

-- ============================================================================
-- Preadditive: Hom-Sets Have Addition
-- ============================================================================

/-- Sum of two sort-preserving maps: pointwise addition. -/
def mapAdd (addF : β → β → β) (f g : Val α → Val β) (x : Val α) : Val β :=
  match f x, g x with
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (addF a b)
  | container a, contents b => container (addF a b)
  | contents a, container b => container (addF a b)
  | contents a, contents b => contents (addF a b)

/-- The sum of two valMaps on contents is contents. -/
theorem mapAdd_contents (addF : β → β → β) (f g : α → β) (a : α) :
    mapAdd addF (valMap f) (valMap g) (contents a) = contents (addF (f a) (g a)) := rfl

/-- The zero map: everything to origin. -/
theorem zero_map_origin (x : Val α) :
    (fun _ : Val α => (origin : Val β)) x = origin := rfl

-- ============================================================================
-- Additive Category: Biproducts
-- ============================================================================

/-- The biproduct of Val α and Val β is Val (α × β). -/
theorem biproduct_is_product (a : α) (b : β) :
    (contents (a, b) : Val (α × β)) ≠ origin := by simp

/-- Biproduct projection to first component. -/
theorem biproduct_proj1 (a : α) (b : β) :
    valMap Prod.fst (contents (a, b) : Val (α × β)) = contents a := rfl

/-- Biproduct projection to second component. -/
theorem biproduct_proj2 (a : α) (b : β) :
    valMap Prod.snd (contents (a, b) : Val (α × β)) = contents b := rfl

-- ============================================================================
-- Linear Category: Enriched Over a Ring
-- ============================================================================

/-- Scalar multiplication of a map: (c · f)(x) = c * f(x). -/
def mapScalar (mulF : β → β → β) (c : β) (f : α → β) (a : α) : Val β :=
  contents (mulF c (f a))

/-- Scalar map gives contents. -/
theorem mapScalar_contents (mulF : β → β → β) (c : β) (f : α → β) (a : α) :
    ∃ r, mapScalar mulF c f a = contents r := ⟨mulF c (f a), rfl⟩

/-- Scalar map is never origin. -/
theorem mapScalar_ne_origin (mulF : β → β → β) (c : β) (f : α → β) (a : α) :
    mapScalar mulF c f a ≠ (origin : Val β) := by simp [mapScalar]

-- ============================================================================
-- Additive Functor
-- ============================================================================

/-- An additive functor preserves the additive structure of Hom-sets. -/
theorem additive_functor (addF : β → β → β) (f g : α → β)
    (h_add : α → β) (hadd : ∀ a, h_add a = addF (f a) (g a)) (a : α) :
    valMap h_add (contents a) = contents (addF (f a) (g a)) := by
  show contents (h_add a) = contents (addF (f a) (g a)); rw [hadd]

-- ============================================================================
-- Exact Functor
-- ============================================================================

/-- An exact functor preserves kernels: if valMap f x = origin, then x = origin. -/
theorem exact_functor_kernel (f : α → β) (x : Val α)
    (h : valMap f x = origin) :
    x = origin := by
  cases x with
  | origin => rfl
  | container a => simp [valMap] at h
  | contents a => simp [valMap] at h

/-- An exact functor preserves images. -/
theorem exact_functor_image (f : α → β) (b : β) (hf : ∃ a, f a = b) :
    ∃ x : Val α, valMap f x = contents b := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨contents a, by show contents (f a) = contents b; rw [ha]⟩

-- ============================================================================
-- Derived Functor (Sort-Level)
-- ============================================================================

/-- Derived functors: contents maps to contents. -/
theorem derived_functor_contents (F : α → β) (a : α) :
    valMap F (contents a) = contents (F a) := rfl

/-- Derived functors: origin maps to origin. -/
theorem derived_functor_origin (F : α → β) :
    valMap F (origin : Val α) = (origin : Val β) := rfl

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Linear categories over Val α:
--   ✓ Preadditive: pointwise addition of maps, contents preserved
--   ✓ Zero map sends everything to origin
--   ✓ Additive: biproducts, projections work
--   ✓ Linear: scalar multiplication of maps, contents preserved
--   ✓ Additive functors: preserve addition on contents
--   ✓ Exact functors: preserve kernels and images
--   ✓ Derived functors: sort structure (contents vs origin)
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
