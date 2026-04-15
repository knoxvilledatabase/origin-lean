/-
Extracted from CategoryTheory/Sites/PreservesSheafification.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Functors which preserve sheafification

In this file, given a Grothendieck topology `J` on `C` and `F : A ⥤ B`,
we define a type class `J.PreservesSheafification F`. We say that `F` preserves
the sheafification if whenever a morphism of presheaves `P₁ ⟶ P₂` induces
an isomorphism on the associated sheaves, then the induced map `P₁ ⋙ F ⟶ P₂ ⋙ F`
also induces an isomorphism on the associated sheaves. (Note: it suffices to check
this property for the map from any presheaf `P` to its associated sheaf, see
`GrothendieckTopology.preservesSheafification_iff_of_adjunctions`).

In general, we define `Sheaf.composeAndSheafify J F : Sheaf J A ⥤ Sheaf J B` as the functor
which sends a sheaf `G` to the sheafification of the composition `G.val ⋙ F`.
If `J.PreservesSheafification F`, we show that this functor can also be thought of
as the localization of the functor `_ ⋙ F` on presheaves: we construct an isomorphism
`presheafToSheafCompComposeAndSheafifyIso` between
`presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F` and
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B`.

Moreover, if we assume `J.HasSheafCompose F`, we obtain an isomorphism
`sheafifyComposeIso J F P : sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F`.

We show that under suitable assumptions, the forgetful functor from a concrete
category preserves sheafification; this holds more generally for
functors between such concrete categories which commute both with
suitable limits and colimits.

## TODO
* construct an isomorphism `Sheaf.composeAndSheafify J F ≅ sheafCompose J F`

-/

universe v u

namespace CategoryTheory

open Category Limits Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)

namespace GrothendieckTopology

class PreservesSheafification : Prop where
  le : J.W ≤ J.W.inverseImage ((whiskeringRight Cᵒᵖ A B).obj F)

variable [PreservesSheafification J F]

lemma W_of_preservesSheafification
    {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) (hf : J.W f) :
    J.W (whiskerRight f F) :=
  PreservesSheafification.le _ hf

variable [HasWeakSheafify J B]

lemma W_isInvertedBy_whiskeringRight_presheafToSheaf :
    J.W.IsInvertedBy (((whiskeringRight Cᵒᵖ A B).obj F) ⋙ presheafToSheaf J B) := by
  intro P₁ P₂ f hf
  dsimp
  rw [← W_iff]
  exact J.W_of_preservesSheafification F _ hf

end GrothendieckTopology

variable [HasWeakSheafify J B]

noncomputable abbrev Sheaf.composeAndSheafify : Sheaf J A ⥤ Sheaf J B :=
  sheafToPresheaf J A ⋙ (whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B

variable [HasWeakSheafify J A]
