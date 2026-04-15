/-
Extracted from CategoryTheory/Conj.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Conjugate morphisms by isomorphisms

An isomorphism `α : X ≅ Y` defines
- a monoid isomorphism
  `CategoryTheory.Iso.conj : End X ≃* End Y` by `α.conj f = α.inv ≫ f ≫ α.hom`;
- a group isomorphism `CategoryTheory.Iso.conjAut : Aut X ≃* Aut Y` by
  `α.conjAut f = α.symm ≪≫ f ≪≫ α`
  using
  `CategoryTheory.Iso.homCongr : (X ≅ X₁) → (Y ≅ Y₁) → (X ⟶ Y) ≃ (X₁ ⟶ Y₁)`
  and `CategoryTheory.Iso.isoCongr : (f : X₁ ≅ X₂) → (g : Y₁ ≅ Y₂) → (X₁ ≅ Y₁) ≃ (X₂ ≅ Y₂)`
  which are defined in  `CategoryTheory.HomCongr`.
-/

universe v u

namespace CategoryTheory

namespace Iso

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (α : X ≅ Y)

def conj : End X ≃* End Y :=
  { homCongr α α with map_mul' := fun f g => homCongr_comp α α α g f }
