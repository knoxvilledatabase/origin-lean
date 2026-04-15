/-
Extracted from CategoryTheory/Limits/Indization/LocallySmall.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# There are only `v`-many natural transformations between Ind-objects

We provide the instance `LocallySmall.{v} (FullSubcategory (IsIndObject (C := C)))`, which will
serve as the basis for our definition of the category of Ind-objects.

## Future work

The equivalence established here serves as the basis for a well-known calculation of hom-sets of
ind-objects as a limit of a colimit.
-/

open CategoryTheory Limits Opposite

universe v v₁ v₂ u u₁ u₂

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

variable {I : Type u₁} [Category.{v₁} I] [HasColimitsOfShape I (Type v)]
  [HasLimitsOfShape Iᵒᵖ (Type v)]

variable {J : Type u₂} [Category.{v₂} J]
  [HasLimitsOfShape Iᵒᵖ (Type (max u v))]

variable (F : I ⥤ C) (G : Cᵒᵖ ⥤ Type v)

noncomputable def colimitYonedaHomEquiv :
    (colimit (F ⋙ yoneda) ⟶ G) ≃ (limit (F.op ⋙ G)) :=
  Equiv.symm <| Equiv.ulift.symm.trans <| Equiv.symm <| Iso.toEquiv <| calc
  (colimit (F ⋙ yoneda) ⟶ G) ≅ limit (F.op ⋙ G ⋙ uliftFunctor.{u}) :=
        colimitYonedaHomIsoLimitOp _ _
  _ ≅ limit ((F.op ⋙ G) ⋙ uliftFunctor.{u}) :=
        HasLimit.isoOfNatIso (Functor.associator _ _ _).symm
  _ ≅ uliftFunctor.{u}.obj (limit (F.op ⋙ G)) :=
        (preservesLimitIso _ _).symm

attribute [elementwise] HasLimit.isoOfNatIso_hom_π

unif_hint {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (G : D ⥤ Type*) (X X' : C)

  where X ≟ X'⊢ (F ⋙ G).obj X ≟ (G.obj (F.obj X)) in
