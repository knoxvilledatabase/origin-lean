/-
Extracted from CategoryTheory/Comma/Presheaf/Colimit.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relative Yoneda preserves certain colimits

In this file we turn the statement `yonedaYonedaColimit` from
`CategoryTheory.Limits.Preserves.Yoneda` from a functor `F : J ⥤ Cᵒᵖ ⥤ Type v` into a statement
about families of presheaves over `A`, i.e., functors `F : J ⥤ Over A`.
-/

namespace CategoryTheory

open Category Opposite Limits

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}

variable {J : Type v} [SmallCategory J] {A : Cᵒᵖ ⥤ Type v} (F : J ⥤ Over A)

local notation "E" => Equivalence.functor (overEquivPresheafCostructuredArrow A)

local notation "E.obj" =>

  Functor.obj (Equivalence.functor (overEquivPresheafCostructuredArrow A))

noncomputable def CostructuredArrow.toOverCompYonedaColimit :
    (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj (colimit F) ≅
    (CostructuredArrow.toOver yoneda A).op ⋙ colimit (F ⋙ yoneda) := calc
  (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj (colimit F)
    ≅ yoneda.op ⋙ yoneda.obj (E.obj (colimit F)) :=
        CostructuredArrow.toOverCompYoneda A _
  _ ≅ yoneda.op ⋙ yoneda.obj (colimit (F ⋙ E)) :=
        Functor.isoWhiskerLeft yoneda.op (yoneda.mapIso (preservesColimitIso E F))
  _ ≅ yoneda.op ⋙ colimit ((F ⋙ E) ⋙ yoneda) :=
        yonedaYonedaColimit _
  _ ≅ yoneda.op ⋙ ((F ⋙ E) ⋙ yoneda).flip ⋙ colim :=
        Functor.isoWhiskerLeft _ (colimitIsoFlipCompColim _)
  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj E) ⋙
          (Functor.whiskeringLeft _ _ _).obj F ⋙ colim :=
        Iso.refl _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ coyoneda ⋙
          (Functor.whiskeringLeft _ _ _).obj F ⋙ colim :=
        Functor.isoWhiskerRight (CostructuredArrow.toOverCompCoyoneda _).symm _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ (F ⋙ yoneda).flip ⋙ colim :=
        Iso.refl _
  _ ≅ (CostructuredArrow.toOver yoneda A).op ⋙ colimit (F ⋙ yoneda) :=
      Functor.isoWhiskerLeft _ (colimitIsoFlipCompColim _).symm

end CategoryTheory
