/-
Extracted from CategoryTheory/Enriched/FunctorCategory.lean
Genuine: 16 of 17 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.CategoryTheory.Enriched.Ordinary
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Functor categories are enriched

If `C` is a `V`-enriched ordinary category, then `J ⥤ C` is also
a `V`-enriched ordinary category, provided `C` has suitable limits.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Enriched.FunctorCategory

open Category MonoidalCategory Limits

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
  {C : Type u₂} [Category.{v₂} C]
  {J : Type u₃} [Category.{v₃} J] [EnrichedOrdinaryCategory V C]

variable (F₁ F₂ F₃ F₄ : J ⥤ C)

@[simps!]
def diagram : Jᵒᵖ ⥤ J ⥤ V := F₁.op ⋙ eHomFunctor V C ⋙ (whiskeringLeft J C V).obj F₂

abbrev HasEnrichedHom := HasEnd (diagram V F₁ F₂)

section

variable [HasEnrichedHom V F₁ F₂]

noncomputable abbrev enrichedHom : V := end_ (diagram V F₁ F₂)

noncomputable abbrev enrichedHomπ (j : J) : enrichedHom V F₁ F₂ ⟶ F₁.obj j ⟶[V] F₂.obj j :=
  end_.π _ j

@[reassoc]
lemma enrichedHom_condition {i j : J} (f : i ⟶ j) :
    enrichedHomπ V F₁ F₂ i ≫ (ρ_ _).inv ≫
      _ ◁ (eHomEquiv V) (F₂.map f) ≫ eComp V _ _ _  =
    enrichedHomπ V F₁ F₂ j ≫ (λ_ _).inv ≫
      (eHomEquiv V) (F₁.map f) ▷ _ ≫ eComp V _ _ _ :=
  end_.condition (diagram V F₁ F₂) f

variable {F₁ F₂}

noncomputable def homEquiv : (F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂) where
  toFun τ := end_.lift (fun j ↦ eHomEquiv V (τ.app j)) (fun i j f ↦ by
    trans eHomEquiv V (τ.app i ≫ F₂.map f)
    · dsimp
      simp only [eHomEquiv_comp, tensorHom_def_assoc, MonoidalCategory.whiskerRight_id,
        ← unitors_equal, assoc, Iso.inv_hom_id_assoc, eHomWhiskerLeft]
    · dsimp
      simp only [← NatTrans.naturality, eHomEquiv_comp, tensorHom_def', id_whiskerLeft,
        assoc, Iso.inv_hom_id_assoc, eHomWhiskerRight])
  invFun g :=
    { app := fun j ↦ (eHomEquiv V).symm (g ≫ end_.π _ j)
      naturality := fun i j f ↦ (eHomEquiv V).injective (by
        dsimp
        simp only [eHomEquiv_comp, Equiv.apply_symm_apply, Iso.cancel_iso_inv_left]
        conv_rhs =>
          rw [tensorHom_def_assoc, MonoidalCategory.whiskerRight_id_assoc, assoc,
            enrichedHom_condition V F₁ F₂ f]
        conv_lhs =>
          rw [tensorHom_def'_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
            id_whiskerLeft_assoc, id_whiskerLeft_assoc, Iso.inv_hom_id_assoc, unitors_equal]) }
  left_inv τ := by aesop
  right_inv g := by aesop

@[reassoc (attr := simp)]
lemma homEquiv_apply_π (τ : F₁ ⟶ F₂) (j : J) :
    homEquiv V τ ≫ enrichedHomπ V _ _ j = eHomEquiv V (τ.app j) := by
  simp [homEquiv]

end

section

variable [HasEnrichedHom V F₁ F₁]

noncomputable def enrichedId : 𝟙_ V ⟶ enrichedHom V F₁ F₁ := homEquiv _ (𝟙 F₁)

@[reassoc (attr := simp)]
lemma enrichedId_π (j : J) : enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j) := by
  simp [enrichedId]

@[simp]
lemma homEquiv_id : homEquiv V (𝟙 F₁) = enrichedId V F₁ := rfl

end

section

variable [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₁ F₃]

noncomputable def enrichedComp : enrichedHom V F₁ F₂ ⊗ enrichedHom V F₂ F₃ ⟶ enrichedHom V F₁ F₃ :=
  end_.lift (fun j ↦ (end_.π _ j ⊗ end_.π _ j) ≫ eComp V _ _ _) (fun i j f ↦ by
    dsimp
    trans (end_.π (diagram V F₁ F₂) i ⊗ end_.π (diagram V F₂ F₃) j) ≫
      (ρ_ _).inv ▷ _ ≫ (_ ◁ (eHomEquiv V (F₂.map f))) ▷ _ ≫ eComp V _ (F₂.obj i) _ ▷ _ ≫
        eComp V _ (F₂.obj j) _
    · have := end_.condition (diagram V F₂ F₃) f
      dsimp [eHomWhiskerLeft, eHomWhiskerRight] at this ⊢
      conv_lhs => rw [assoc, tensorHom_def_assoc]
      conv_rhs =>
        rw [tensorHom_def_assoc, whisker_assoc_assoc, e_assoc,
          triangle_assoc_comp_right_inv_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
          assoc, assoc, ← this, MonoidalCategory.whiskerLeft_comp_assoc,
          MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
          ← e_assoc, whiskerLeft_rightUnitor_inv_assoc, associator_inv_naturality_right_assoc,
          Iso.hom_inv_id_assoc, whisker_exchange_assoc, MonoidalCategory.whiskerRight_id_assoc,
          Iso.inv_hom_id_assoc]
    · have := end_.condition (diagram V F₁ F₂) f
      dsimp [eHomWhiskerLeft, eHomWhiskerRight] at this ⊢
      conv_lhs =>
        rw [tensorHom_def'_assoc, ← comp_whiskerRight_assoc,
          ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
          assoc, assoc, this, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
          comp_whiskerRight_assoc, leftUnitor_inv_whiskerRight_assoc,
          ← associator_inv_naturality_left_assoc, ← e_assoc',
          Iso.inv_hom_id_assoc, ← whisker_exchange_assoc, id_whiskerLeft_assoc,
          Iso.inv_hom_id_assoc]
      conv_rhs => rw [assoc, tensorHom_def'_assoc])

@[reassoc (attr := simp)]
lemma enrichedComp_π (j : J) :
    enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j =
      (end_.π (diagram V F₁ F₂) j ⊗ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ _ _ := by
  simp [enrichedComp]

variable {F₁ F₂ F₃}

@[reassoc]
lemma homEquiv_comp (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    (homEquiv V) (f ≫ g) = (λ_ (𝟙_ V)).inv ≫ ((homEquiv V) f ⊗ (homEquiv V) g) ≫
    enrichedComp V F₁ F₂ F₃ := by
  ext j
  simp only [homEquiv_apply_π, NatTrans.comp_app, eHomEquiv_comp, assoc,
    enrichedComp_π, Functor.op_obj, ← tensor_comp_assoc]

end

@[reassoc (attr := simp)]
lemma enriched_id_comp [HasEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₂] :
    (λ_ (enrichedHom V F₁ F₂)).inv ≫ enrichedId V F₁ ▷ enrichedHom V F₁ F₂ ≫
      enrichedComp V F₁ F₁ F₂ = 𝟙 _ := by
  ext j
  rw [assoc, assoc, enrichedComp_π, id_comp, tensorHom_def, assoc,
    ← comp_whiskerRight_assoc, enrichedId_π, ← whisker_exchange_assoc,
    id_whiskerLeft, assoc, assoc, Iso.inv_hom_id_assoc]
  dsimp
  rw [e_id_comp, comp_id]

@[reassoc (attr := simp)]
lemma enriched_comp_id [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₂] :
    (ρ_ (enrichedHom V F₁ F₂)).inv ≫ enrichedHom V F₁ F₂ ◁ enrichedId V F₂ ≫
      enrichedComp V F₁ F₂ F₂ = 𝟙 _ := by
  ext j
  rw [assoc, assoc, enrichedComp_π, id_comp, tensorHom_def', assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, enrichedId_π,
    whisker_exchange_assoc, MonoidalCategory.whiskerRight_id, assoc, assoc,
    Iso.inv_hom_id_assoc]
  dsimp
  rw [e_comp_id, comp_id]

@[reassoc]
lemma enriched_assoc [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₃] [HasEnrichedHom V F₁ F₄]
    [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₂ F₄] [HasEnrichedHom V F₃ F₄] :
    (α_ (enrichedHom V F₁ F₂) (enrichedHom V F₂ F₃) (enrichedHom V F₃ F₄)).inv ≫
      enrichedComp V F₁ F₂ F₃ ▷ enrichedHom V F₃ F₄ ≫ enrichedComp V F₁ F₃ F₄ =
      enrichedHom V F₁ F₂ ◁ enrichedComp V F₂ F₃ F₄ ≫ enrichedComp V F₁ F₂ F₄ := by
  ext j
  conv_lhs =>
    rw [assoc, assoc, enrichedComp_π,
      tensorHom_def_assoc, ← comp_whiskerRight_assoc, enrichedComp_π,
      comp_whiskerRight_assoc, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, ← tensorHom_def'_assoc, ← associator_inv_naturality_assoc]
  conv_rhs =>
    rw [assoc, enrichedComp_π, tensorHom_def'_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      enrichedComp_π, MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange_assoc,
      whisker_exchange_assoc, ← tensorHom_def_assoc]
  dsimp
  rw [e_assoc]

variable (J C)

noncomputable def enrichedOrdinaryCategory [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂] :
    EnrichedOrdinaryCategory V (J ⥤ C) where
  Hom F₁ F₂ := enrichedHom V F₁ F₂
  id F := enrichedId V F
  comp F₁ F₂ F₃ := enrichedComp V F₁ F₂ F₃
  assoc _ _ _ _ := enriched_assoc _ _ _ _ _
  homEquiv := homEquiv V
  homEquiv_id _ := homEquiv_id V _
  homEquiv_comp f g := homEquiv_comp V f g

end CategoryTheory.Enriched.FunctorCategory
