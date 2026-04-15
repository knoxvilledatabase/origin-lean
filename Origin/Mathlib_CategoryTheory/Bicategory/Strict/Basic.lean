/-
Extracted from CategoryTheory/Bicategory/Strict/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Strict bicategories

A bicategory is called `Strict` if the left unitors, the right unitors, and the associators are
isomorphisms given by equalities.

## Implementation notes

In the literature of category theory, a strict bicategory (usually called a strict 2-category) is
often defined as a bicategory whose left unitors, right unitors, and associators are identities.
We cannot use this definition directly here since the types of 2-morphisms depend on 1-morphisms.
For this reason, we use `eqToIso`, which gives isomorphisms from equalities, instead of
identities.
-/

namespace CategoryTheory

open Bicategory

universe w v u

variable (B : Type u) [Bicategory.{w, v} B]

class Bicategory.Strict : Prop where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {a b : B} (f : a ⟶ b), 𝟙 a ≫ f = f := by cat_disch
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {a b : B} (f : a ⟶ b), f ≫ 𝟙 b = f := by cat_disch
  /-- Composition in a bicategory is associative. -/
  assoc : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    cat_disch
  /-- The left unitors are given by equalities -/
  leftUnitor_eqToIso : ∀ {a b : B} (f : a ⟶ b), λ_ f = eqToIso (id_comp f) := by cat_disch
  /-- The right unitors are given by equalities -/
  rightUnitor_eqToIso : ∀ {a b : B} (f : a ⟶ b), ρ_ f = eqToIso (comp_id f) := by cat_disch
  /-- The associators are given by equalities -/
  associator_eqToIso :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), α_ f g h = eqToIso (assoc f g h) := by
    cat_disch

-- INSTANCE (free from Core): (priority

namespace Bicategory

variable {B}
