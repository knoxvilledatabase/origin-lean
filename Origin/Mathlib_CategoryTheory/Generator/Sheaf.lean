/-
Extracted from CategoryTheory/Generator/Sheaf.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Generators in the category of sheaves

In this file, we show that if `J : GrothendieckTopology C` and `A` is a preadditive
category which has a separator (and suitable coproducts), then `Sheaf J A` has a separator.

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

namespace Sheaf

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{v} A] [HasWeakSheafify J A]

noncomputable def freeYoneda (X : C) (M : A) : Sheaf J A :=
  (presheafToSheaf J A).obj (Presheaf.freeYoneda X M)

variable {J} in

noncomputable def freeYonedaHomEquiv {X : C} {M : A} {F : Sheaf J A} :
    (freeYoneda J X M ⟶ F) ≃ (M ⟶ F.obj.obj (op X)) :=
  ((sheafificationAdjunction J A).homEquiv _ _).trans Presheaf.freeYonedaHomEquiv

set_option backward.isDefEq.respectTransparency false in

lemma isSeparating {ι : Type w} {S : ι → A} (hS : ObjectProperty.IsSeparating (.ofObj S)) :
    ObjectProperty.IsSeparating (.ofObj (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))) := by
  intro F G f g hfg
  refine (sheafToPresheaf J A).map_injective (Presheaf.isSeparating C hS _ _ ?_)
  rintro _ ⟨X, i⟩ a
  apply ((sheafificationAdjunction _ _).homEquiv _ _).symm.injective
  simpa only [← Adjunction.homEquiv_naturality_right_symm] using
    hfg _ (ObjectProperty.ofObj_apply _ ⟨X, i⟩)
      (((sheafificationAdjunction _ _).homEquiv _ _).symm a)

lemma isSeparator {ι : Type w} {S : ι → A} (hS : ObjectProperty.IsSeparating (.ofObj S))
    [HasCoproduct (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))] [Preadditive A] :
    IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))) :=
  (isSeparating J hS).isSeparator_coproduct

variable (A) in

-- INSTANCE (free from Core): hasSeparator

end Sheaf

end CategoryTheory
