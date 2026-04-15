/-
Extracted from CategoryTheory/Functor/KanExtension/Dense.lean
Genuine: 9 of 14 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Dense functors

A functor `F : C ⥤ D` is dense (`F.IsDense`) if `𝟭 D` is a pointwise
left Kan extension of `F` along itself, i.e. any `Y : D` is the
colimit of all `F.obj X` for all morphisms `F.obj X ⟶ Y` (which
is the condition `F.DenseAt Y`).
When `F` is full, we show that this
is equivalent to saying that the restricted Yoneda functor
`D ⥤ Cᵒᵖ ⥤ Type _` is fully faithful (see the lemma
`Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda`).

We also show that the range of a dense functor is a strong
generator (see `Functor.isStrongGenerator_of_isDense`).

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite Presheaf ConcreteCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C']

namespace Functor

class IsDense (F : C ⥤ D) : Prop where
  isDenseAt (F) (Y : D) : F.isDenseAt Y

noncomputable def denseAt (F : C ⥤ D) [F.IsDense] (Y : D) : F.DenseAt Y :=
  (IsDense.isDenseAt F Y).some

lemma isDense_iff_nonempty_isPointwiseLeftKanExtension (F : C ⥤ D) :
    F.IsDense ↔
      Nonempty ((LeftExtension.mk _ (rightUnitor F).inv).IsPointwiseLeftKanExtension) :=
  ⟨fun _ ↦ ⟨fun _ ↦ F.denseAt _⟩, fun ⟨h⟩ ↦ ⟨fun _ ↦ ⟨h _⟩⟩⟩

lemma IsDense.of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsDense] :
    G.IsDense where
  isDenseAt Y := by
    rw [← Functor.congr_isDenseAt e]
    exact ⟨F.denseAt Y⟩

lemma IsDense.iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsDense ↔ G.IsDense :=
  ⟨fun _ ↦ of_iso e, fun _ ↦ of_iso e.symm⟩

variable (F : C ⥤ D)

-- INSTANCE (free from Core): (G

lemma IsDense.comp_left_iff_of_isEquivalence (G : C' ⥤ C) [G.IsEquivalence] :
    (G ⋙ F).IsDense ↔ F.IsDense := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let e : G.inv ⋙ G ⋙ F ≅ F := (associator _ _ _).symm ≪≫
    isoWhiskerRight (G.asEquivalence.counitIso) _ ≪≫ F.leftUnitor
  exact of_iso e

-- INSTANCE (free from Core): (G

lemma IsDense.comp_right_iff_of_isEquivalence (G : D ⥤ C') [G.IsEquivalence] :
    (F ⋙ G).IsDense ↔ F.IsDense := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let e : (F ⋙ G) ⋙ G.inv ≅ F := associator .. ≪≫
    isoWhiskerLeft _ G.asEquivalence.unitIso.symm ≪≫ F.rightUnitor
  exact of_iso e

-- INSTANCE (free from Core): [F.IsDense]

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): [F.IsDense]

set_option backward.isDefEq.respectTransparency false in

variable {F} in

lemma isDense_iff_fullyFaithful_restrictedULiftYoneda [F.Full] :
    F.IsDense ↔ Nonempty (restrictedULiftYoneda.{w} F).FullyFaithful :=
  ⟨fun _ ↦ ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ ↦ IsDense.of_fullyFaithful_restrictedULiftYoneda h⟩

open ObjectProperty in

lemma isStrongGenerator_of_isDense [F.IsDense] :
    IsStrongGenerator (.ofObj F.obj) :=
  (IsStrongGenerator.mk_of_exists_colimitsOfShape.{max u₁ u₂ v₁ v₂,
      max u₁ v₁ v₂} (fun Y ↦ ⟨_, _, ⟨{
    ι := _
    diag := _
    isColimit := (IsColimit.whiskerEquivalence (F.denseAt Y)
      ((ShrinkHoms.equivalence _).symm.trans ((Shrink.equivalence _)).symm))
    prop_diag_obj := by simp }⟩⟩))

end Functor

end CategoryTheory
