/-
Extracted from CategoryTheory/Limits/Types/Limits.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Limits in the category of types.

We show that the category of types has all limits, by providing the usual concrete models.

-/

universe u' v u w

namespace CategoryTheory.Limits.Types

open ConcreteCategory

section limit_characterization

variable {J : Type v} [Category.{w} J] {F : J ⥤ Type u}

def coneOfSection {s} (hs : s ∈ F.sections) : Cone F where
  pt := PUnit
  π := { app j := TypeCat.ofHom (fun _ ↦ s j), naturality _ _ f := by ext; exact (hs f).symm }

def sectionOfCone (c : Cone F) (x : c.pt) : F.sections :=
  ⟨fun j ↦ c.π.app j x, fun f ↦ congr_hom (c.π.naturality f).symm x⟩

theorem isLimit_iff (c : Cone F) :
    Nonempty (IsLimit c) ↔ ∀ s ∈ F.sections, ∃! x : c.pt, ∀ j, c.π.app j x = s j := by
  refine ⟨fun ⟨t⟩ s hs ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · let cs := coneOfSection hs
    exact ⟨t.lift cs ⟨⟩, fun j ↦ congr_hom (t.fac cs j) ⟨⟩,
      fun x hx ↦ congr_hom (CC := fun X ↦ X)
        (t.uniq cs (TypeCat.ofHom (fun _ ↦ x)) fun j ↦ by ext; exact hx j) ⟨⟩⟩
  · have := fun c y ↦ h _ (sectionOfCone c y).2
    choose x hx using fun c y ↦ h _ (sectionOfCone c y).2
    exact ⟨fun d ↦ TypeCat.ofHom (x d), fun c j ↦ by ext y; exact (hx c y).1 j,
      fun c f hf ↦ by ext y; exact (hx c y).2 (f y) (fun j ↦ congr_hom (hf j) y)⟩

theorem isLimit_iff_bijective_sectionOfCone (c : Cone F) :
    Nonempty (IsLimit c) ↔ (Types.sectionOfCone c).Bijective := by
  simp_rw [isLimit_iff, Function.bijective_iff_existsUnique, Subtype.forall, F.sections_ext_iff,
    sectionOfCone]

noncomputable def isLimitEquivSections {c : Cone F} (t : IsLimit c) :
    c.pt ≃ F.sections where
  toFun := sectionOfCone c
  invFun s := t.lift (coneOfSection s.2) ⟨⟩
  left_inv x := (congr_hom (t.uniq (coneOfSection _)
    (TypeCat.ofHom (fun _ ↦ x)) fun _ ↦ rfl) ⟨⟩).symm
  right_inv s := Subtype.ext (funext fun j ↦ congr_hom (t.fac (coneOfSection s.2) j) ⟨⟩)
