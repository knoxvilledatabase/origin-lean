/-
Extracted from CategoryTheory/Monoidal/Bimod.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of bimodule objects over a pair of monoid objects.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory MonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

open CategoryTheory.Limits

variable [HasCoequalizers C]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

theorem id_tensor_π_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Z ⊗ Y ⟶ W)
    (wh : (Z ◁ f) ≫ h = (Z ◁ g) ≫ h) :
    (Z ◁ coequalizer.π f g) ≫
        (PreservesCoequalizer.iso (tensorLeft Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorLeft Z) f g h wh

theorem id_tensor_π_preserves_coequalizer_inv_colimMap_desc {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
    (f' g' : X' ⟶ Y') (p : Z ⊗ X ⟶ X') (q : Z ⊗ Y ⟶ Y') (wf : (Z ◁ f) ≫ q = p ≫ f')
    (wg : (Z ◁ g) ≫ q = p ≫ g') (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    (Z ◁ coequalizer.π f g) ≫
        (PreservesCoequalizer.iso (tensorLeft Z) f g).inv ≫
          colimMap (parallelPairHom (Z ◁ f) (Z ◁ g) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  map_π_preserves_coequalizer_inv_colimMap_desc (tensorLeft Z) f g f' g' p q wf wg h wh

end

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem π_tensor_id_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Y ⊗ Z ⟶ W)
    (wh : (f ▷ Z) ≫ h = (g ▷ Z) ≫ h) :
    (coequalizer.π f g ▷ Z) ≫
        (PreservesCoequalizer.iso (tensorRight Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorRight Z) f g h wh

theorem π_tensor_id_preserves_coequalizer_inv_colimMap_desc {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
    (f' g' : X' ⟶ Y') (p : X ⊗ Z ⟶ X') (q : Y ⊗ Z ⟶ Y') (wf : (f ▷ Z) ≫ q = p ≫ f')
    (wg : (g ▷ Z) ≫ q = p ≫ g') (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    (coequalizer.π f g ▷ Z) ≫
        (PreservesCoequalizer.iso (tensorRight Z) f g).inv ≫
          colimMap (parallelPairHom (f ▷ Z) (g ▷ Z) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  map_π_preserves_coequalizer_inv_colimMap_desc (tensorRight Z) f g f' g' p q wf wg h wh

end

end

structure Bimod (A B : Mon C) where
  /-- The underlying monoidal category -/
  X : C
  /-- The left action of this bimodule object -/
  actLeft : A.X ⊗ X ⟶ X
  one_actLeft : η ▷ X ≫ actLeft = (λ_ X).hom := by cat_disch
  left_assoc :
    μ ▷ X ≫ actLeft = (α_ A.X A.X X).hom ≫ A.X ◁ actLeft ≫ actLeft := by cat_disch
  /-- The right action of this bimodule object -/
  actRight : X ⊗ B.X ⟶ X
  actRight_one : X ◁ η ≫ actRight = (ρ_ X).hom := by cat_disch
  right_assoc :
    X ◁ μ ≫ actRight = (α_ X B.X B.X).inv ≫ actRight ▷ B.X ≫ actRight := by
    cat_disch
  middle_assoc :
    actLeft ▷ B.X ≫ actRight = (α_ A.X X B.X).hom ≫ A.X ◁ actRight ≫ actLeft := by
    cat_disch

attribute [reassoc (attr := simp)] Bimod.one_actLeft Bimod.actRight_one Bimod.left_assoc

  Bimod.right_assoc Bimod.middle_assoc

namespace Bimod

variable {A B : Mon C} (M : Bimod A B)
