/-
Extracted from CategoryTheory/Sites/Coherent/LocallySurjective.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# Locally surjective morphisms of coherent sheaves

This file characterises locally surjective morphisms of presheaves for the coherent, regular
and extensive topologies.

## Main results

* `regularTopology.isLocallySurjective_iff` A morphism of presheaves `f : F ⟶ G` is locally
  surjective for the regular topology iff for every object `X` of `C`, and every `y : G(X)`, there
  is an effective epimorphism `φ : X' ⟶ X` and an `x : F(X)` such that `f_{X'}(x) = G(φ)(y)`.

* `coherentTopology.isLocallySurjective_iff` a morphism of sheaves for the coherent topology on a
  preregular finitary extensive category is locally surjective if and only if it is
  locally surjective for the regular topology.

* `extensiveTopology.isLocallySurjective_iff` a morphism of sheaves for the extensive topology on a
  finitary extensive category is locally surjective iff it is objectwise surjective.
-/

universe w

open CategoryTheory Sheaf Limits Opposite

namespace CategoryTheory

variable {C : Type*} (D : Type*) [Category* C] [Category* D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

set_option backward.isDefEq.respectTransparency false in

lemma extensiveTopology.presheafIsLocallySurjective_iff [FinitaryPreExtensive C] {F G : Cᵒᵖ ⥤ D}
    (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      [PreservesFiniteProducts (forget D)] : Presheaf.IsLocallySurjective (extensiveTopology C) f ↔
        ∀ (X : C), Function.Surjective (f.app (op X)) := by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget (J := extensiveTopology C)]
    exact fun h _ ↦
      surjective_of_isLocallySurjective_sheaf_of_types (Functor.whiskerRight f (forget D)) h
  · exact fun a ↦
      Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ a _)

lemma extensiveTopology.isLocallySurjective_iff [FinitaryExtensive C]
    {F G : Sheaf (extensiveTopology C) D} (f : F ⟶ G)
      [PreservesFiniteProducts (forget D)] : IsLocallySurjective f ↔
        ∀ (X : C), Function.Surjective (f.hom.app (op X)) :=
  extensiveTopology.presheafIsLocallySurjective_iff _ f.hom

set_option backward.isDefEq.respectTransparency false in

lemma coherentTopology.presheafIsLocallySurjective_iff {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G)
    [Preregular C] [FinitaryPreExtensive C] [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      [PreservesFiniteProducts (forget D)] :
        Presheaf.IsLocallySurjective (coherentTopology C) f ↔
          Presheaf.IsLocallySurjective (regularTopology C) f := by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget,
      Presheaf.isLocallySurjective_iff_whisker_forget (J := regularTopology C)]
    exact regularTopology.isLocallySurjective_sheaf_of_types _
  · refine Presheaf.isLocallySurjective_of_le (J := regularTopology C) ?_ _
    rw [← extensive_regular_generate_coherent]
    exact (Coverage.gi _).gc.monotone_l le_sup_right

lemma coherentTopology.isLocallySurjective_iff [Preregular C] [FinitaryExtensive C]
    {F G : Sheaf (coherentTopology C) D} (f : F ⟶ G) [PreservesFiniteProducts (forget D)] :
      IsLocallySurjective f ↔ Presheaf.IsLocallySurjective (regularTopology C) f.hom :=
  presheafIsLocallySurjective_iff _ f.hom

end CategoryTheory
