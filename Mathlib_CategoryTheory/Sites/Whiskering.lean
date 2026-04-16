/-
Extracted from CategoryTheory/Sites/Whiskering.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.CategoryTheory.Sites.Sheaf

noncomputable section

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

open CategoryTheory.Limits

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

@[simps]
def sheafCompose : Sheaf J A ⥤ Sheaf J B where
  obj G := ⟨G.val ⋙ F, GrothendieckTopology.HasSheafCompose.isSheaf G.val G.2⟩
  map η := ⟨whiskerRight η.val _⟩
  map_id _ := Sheaf.Hom.ext <| whiskerRight_id _
  map_comp _ _ := Sheaf.Hom.ext <| whiskerRight_comp _ _ _

instance [F.Faithful] : (sheafCompose J F ⋙ sheafToPresheaf _ _).Faithful :=
  show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Faithful from inferInstance

instance [F.Faithful] [F.Full] : (sheafCompose J F ⋙ sheafToPresheaf _ _).Full :=
  show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Full from inferInstance

instance [F.Faithful] : (sheafCompose J F).Faithful :=
  Functor.Faithful.of_comp (sheafCompose J F) (sheafToPresheaf _ _)

instance [F.Full] [F.Faithful] : (sheafCompose J F).Full :=
  Functor.Full.of_comp_faithful (sheafCompose J F) (sheafToPresheaf _ _)

instance [F.ReflectsIsomorphisms] : (sheafCompose J F).ReflectsIsomorphisms where
  reflects {G₁ G₂} f _ := by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _),
      ← isIso_iff_of_reflects_iso _ ((whiskeringRight Cᵒᵖ A B).obj F)]
    change IsIso ((sheafToPresheaf _ _).map ((sheafCompose J F).map f))
    infer_instance

variable {F G}

def sheafCompose_map : sheafCompose J F ⟶ sheafCompose J G where
  app := fun _ => .mk <| whiskerLeft _ η

@[simp]
lemma sheafCompose_id : sheafCompose_map (F := F) J (𝟙 _) = 𝟙 _ := rfl

@[simp]
lemma sheafCompose_comp :
    sheafCompose_map J (η ≫ γ) = sheafCompose_map J η ≫ sheafCompose_map J γ := rfl

namespace GrothendieckTopology.Cover

variable (F G) {J}

variable (P : Cᵒᵖ ⥤ A) {X : C} (S : J.Cover X)

@[simps!]
def multicospanComp : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F :=
  NatIso.ofComponents
    (fun t =>
      match t with
      | WalkingMulticospan.left _ => Iso.refl _
      | WalkingMulticospan.right _ => Iso.refl _)
    (by
      rintro (a | b) (a | b) (f | f | f)
      all_goals aesop_cat)

def mapMultifork :
    F.mapCone (S.multifork P) ≅
      (Limits.Cones.postcompose (S.multicospanComp F P).hom).obj (S.multifork (P ⋙ F)) :=
  Cones.ext (Iso.refl _)

end GrothendieckTopology.Cover

instance hasSheafCompose_of_preservesMulticospan (F : A ⥤ B)
    [∀ (X : C) (S : J.Cover X) (P : Cᵒᵖ ⥤ A), PreservesLimit (S.index P).multicospan F] :
    J.HasSheafCompose F where
  isSheaf P hP := by
    rw [Presheaf.isSheaf_iff_multifork] at hP ⊢
    intro X S
    obtain ⟨h⟩ := hP X S
    replace h := isLimitOfPreserves F h
    replace h := Limits.IsLimit.ofIsoLimit h (S.mapMultifork F P)
    exact ⟨Limits.IsLimit.postcomposeHomEquiv (S.multicospanComp F P) _ h⟩

instance hasSheafCompose_of_preservesLimitsOfSize [PreservesLimitsOfSize.{v₁, max u₁ v₁} F] :
    J.HasSheafCompose F where
  isSheaf _ hP := Presheaf.isSheaf_comp_of_isSheaf J _ F hP

variable {J}

lemma Sheaf.isSeparated [ConcreteCategory A] [J.HasSheafCompose (forget A)]
    (F : Sheaf J A) : Presheaf.IsSeparated J F.val := by
  rintro X S hS x y h
  exact (Presieve.isSeparated_of_isSheaf _ _ ((isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose J (forget A)).obj F).2) S hS).ext (fun _ _ hf => h _ _ hf)

lemma Presheaf.IsSheaf.isSeparated {F : Cᵒᵖ ⥤ A} [ConcreteCategory A]
    [J.HasSheafCompose (forget A)] (hF : Presheaf.IsSheaf J F) :
    Presheaf.IsSeparated J F :=
  Sheaf.isSeparated ⟨F, hF⟩

end CategoryTheory
