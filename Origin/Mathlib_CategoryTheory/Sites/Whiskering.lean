/-
Extracted from CategoryTheory/Sites/Whiskering.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

In this file we construct the functor `Sheaf J A ⥤ Sheaf J B` between sheaf categories
obtained by composition with a functor `F : A ⥤ B`.

In order for the sheaf condition to be preserved, `F` must preserve the correct limits.
The lemma `Presheaf.IsSheaf.comp` says that composition with such an `F` indeed preserves the
sheaf condition.

The functor between sheaf categories is called `sheafCompose J F`.
Given a natural transformation `η : F ⟶ G`, we obtain a natural transformation
`sheafCompose J F ⟶ sheafCompose J G`, which we call `sheafCompose_map J η`.

-/

namespace CategoryTheory

open CategoryTheory.Limits Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {A : Type u₂} [Category.{v₂} A]

variable {B : Type u₃} [Category.{v₃} B]

variable (J : GrothendieckTopology C)

variable {U : C} (R : Presieve U)

variable (F G H : A ⥤ B) (η : F ⟶ G) (γ : G ⟶ H)

class GrothendieckTopology.HasSheafCompose : Prop where
  /-- For every sheaf `P`, `P ⋙ F` is a sheaf. -/
  isSheaf (P : Cᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J P) : Presheaf.IsSheaf J (P ⋙ F)

variable [J.HasSheafCompose F] [J.HasSheafCompose G] [J.HasSheafCompose H]
