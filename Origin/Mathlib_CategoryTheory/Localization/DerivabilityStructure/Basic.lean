/-
Extracted from CategoryTheory/Localization/DerivabilityStructure/Basic.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.Localization.Resolution
import Mathlib.CategoryTheory.GuitartExact.VerticalComposition

/-!
# Derivability structures

Let `Φ : LocalizerMorphism W₁ W₂` be a localizer morphism, i.e. `W₁ : MorphismProperty C₁`,
`W₂ : MorphismProperty C₂`, and `Φ.functor : C₁ ⥤ C₂` is a functors which maps `W₁` to `W₂`.
Following the definition introduced by Bruno Kahn and Georges Maltsiniotis in
[Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008],
we say that `Φ` is a right derivability structure if `Φ` has right resolutions and
the following 2-square is Guitart exact, where `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are
localization functors for `W₁` and `W₂`, and `F : D₁ ⥤ D₂` is the induced functor
on the localized categories:

```
    Φ.functor
  C₁   ⥤   C₂
  |         |
L₁|         | L₂
  v         v
  D₁   ⥤   D₂
       F
```

## Implementation details

In the field `guitartExact'` of the structure `LocalizerMorphism.IsRightDerivabilityStructure`,
The condition that the square is Guitart exact is stated for the localization functors
of the constructed categories (`W₁.Q` and `W₂.Q`).
The lemma `LocalizerMorphism.isRightDerivabilityStructure_iff` show that it does
not depend of the choice of the localization functors.

## TODO

* Construct derived functors using derivability structures
* Define the notion of left derivability structures
* Construct the injective derivability structure in order to derive functor from
the bounded below homotopy category in an abelian category with enough injectives
* Construct the projective derivability structure in order to derive functor from
the bounded above homotopy category in an abelian category with enough projectives
* Construct the flat derivability structure on the bounded above homotopy category
of categories of modules (and categories of sheaves of modules)
* Define the product derivability structure and formalize derived functors of
functors in several variables


## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Localization

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

class IsRightDerivabilityStructure : Prop where
  hasRightResolutions : Φ.HasRightResolutions := by infer_instance
  guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom

attribute [instance] IsRightDerivabilityStructure.hasRightResolutions
  IsRightDerivabilityStructure.guitartExact'

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂] (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] (F : D₁ ⥤ D₂)

lemma isRightDerivabilityStructure_iff [Φ.HasRightResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
    Φ.IsRightDerivabilityStructure ↔ TwoSquare.GuitartExact e.hom := by
  have : Φ.IsRightDerivabilityStructure ↔
      TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom :=
    ⟨fun h => h.guitartExact', fun h => ⟨inferInstance, h⟩⟩
  rw [this]
  let e' := (Φ.catCommSq W₁.Q W₂.Q).iso
  let E₁ := Localization.uniq W₁.Q L₁ W₁
  let E₂ := Localization.uniq W₂.Q L₂ W₂
  let e₁ : W₁.Q ⋙ E₁.functor ≅ L₁ := compUniqFunctor W₁.Q L₁ W₁
  let e₂ : W₂.Q ⋙ E₂.functor ≅ L₂ := compUniqFunctor W₂.Q L₂ W₂
  let e'' : (Φ.functor ⋙ W₂.Q) ⋙ E₂.functor ≅ (W₁.Q ⋙ E₁.functor) ⋙ F :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e₂ ≪≫ e ≪≫ isoWhiskerRight e₁.symm F
  let e''' : Φ.localizedFunctor W₁.Q W₂.Q ⋙ E₂.functor ≅ E₁.functor ⋙ F :=
    liftNatIso W₁.Q W₁ _ _ _ _ e''
  have : TwoSquare.vComp' e'.hom e'''.hom e₁ e₂ = e.hom := by
    ext X₁
    rw [TwoSquare.vComp'_app, liftNatIso_hom, liftNatTrans_app]
    simp only [Functor.comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app,
      whiskerRight_app, id_comp, assoc, e'']
    dsimp [Lifting.iso]
    rw [F.map_id, id_comp, ← F.map_comp, Iso.inv_hom_id_app, F.map_id, comp_id,
      ← Functor.map_comp_assoc]
    erw [show (CatCommSq.iso Φ.functor W₁.Q W₂.Q (localizedFunctor Φ W₁.Q W₂.Q)).hom =
      (Lifting.iso W₁.Q W₁ _ _).inv by rfl, Iso.inv_hom_id_app]
    simp
  rw [← TwoSquare.GuitartExact.vComp'_iff_of_equivalences e'.hom E₁ E₂ e''' e₁ e₂, this]

lemma guitartExact_of_isRightDerivabilityStructure' [h : Φ.IsRightDerivabilityStructure]
    (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) : TwoSquare.GuitartExact e.hom := by
  simpa only [Φ.isRightDerivabilityStructure_iff L₁ L₂ F e] using h

lemma guitartExact_of_isRightDerivabilityStructure [Φ.IsRightDerivabilityStructure] :
    TwoSquare.GuitartExact ((Φ.catCommSq L₁ L₂).iso).hom :=
  guitartExact_of_isRightDerivabilityStructure' _ _ _ _ _

instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).HasRightResolutions :=
  fun X₂ => ⟨RightResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).IsRightDerivabilityStructure := by
  rw [(LocalizerMorphism.id W₁).isRightDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id W₁.Q

end LocalizerMorphism

end CategoryTheory
