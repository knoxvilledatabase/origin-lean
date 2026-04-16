/-
Extracted from CategoryTheory/Limits/Yoneda.lean
Genuine: 9 | Conflates: 0 | Dissolved: 0 | Infrastructure: 17
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.Util.AssertExists

noncomputable section

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `PUnit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/

open Opposite CategoryTheory Limits

universe t w v u

namespace CategoryTheory

namespace Coyoneda

variable {C : Type u} [Category.{v} C]

@[simps]
def colimitCocone (X : Cᵒᵖ) : Cocone (coyoneda.obj X) where
  pt := PUnit
  ι := { app := by aesop_cat }

@[simps]
def colimitCoconeIsColimit (X : Cᵒᵖ) : IsColimit (colimitCocone X) where
  desc s _ := s.ι.app (unop X) (𝟙 _)
  fac s Y := by
    funext f
    convert congr_fun (s.w f).symm (𝟙 (unop X))
    simp only [coyoneda_obj_obj, Functor.const_obj_obj, types_comp_apply,
      coyoneda_obj_map, Category.id_comp]
  uniq s m w := by
    apply funext; rintro ⟨⟩
    dsimp
    rw [← w]
    simp

instance (X : Cᵒᵖ) : HasColimit (coyoneda.obj X) :=
  HasColimit.mk
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

noncomputable def colimitCoyonedaIso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ PUnit := by
  apply colimit.isoColimitCocone
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

end Coyoneda

variable {C : Type u} [Category.{v} C]

open Limits

section

variable {J : Type w} [Category.{t} J]

@[simps]
def Limits.coneOfSectionCompYoneda (F : J ⥤ Cᵒᵖ) (X : C)
    (s : (F ⋙ yoneda.obj X).sections) : Cone F where
  pt := Opposite.op X
  π := compYonedaSectionsEquiv F X s

instance yoneda_preservesLimit (F : J ⥤ Cᵒᵖ) (X : C) :
    PreservesLimit F (yoneda.obj X) where
  preserves {c} hc := by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨(hc.lift (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩)).unop,
      fun j => Quiver.Hom.op_inj (hc.fac (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) j),
      fun m hm => Quiver.Hom.op_inj
        (hc.uniq (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) _
          (fun j => Quiver.Hom.unop_inj (hm j)))⟩

variable (J) in

noncomputable instance yoneda_preservesLimitsOfShape (X : C) :
    PreservesLimitsOfShape J (yoneda.obj X) where

def yonedaJointlyReflectsLimits (F : J ⥤ Cᵒᵖ) (c : Cone F)
    (hc : ∀ X : C, IsLimit ((yoneda.obj X).mapCone c)) : IsLimit c where
  lift s := ((hc s.pt.unop).lift ((yoneda.obj s.pt.unop).mapCone s) (𝟙 _)).op
  fac s j := Quiver.Hom.unop_inj (by
    simpa using congr_fun ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 _))
  uniq s m hm := Quiver.Hom.unop_inj (by
    apply (Types.isLimitEquivSections (hc s.pt.unop)).injective
    ext j
    have eq := congr_fun ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 _)
    dsimp at eq
    dsimp [Types.isLimitEquivSections, Types.sectionOfCone]
    rw [eq, Category.comp_id, ← hm, unop_comp])

noncomputable def Limits.Cocone.isColimitYonedaEquiv {F : J ⥤ C} (c : Cocone F) :
    IsColimit c ≃ ∀ (X : C), IsLimit ((yoneda.obj X).mapCone c.op) where
  toFun h _ := isLimitOfPreserves _ h.op
  invFun h := IsLimit.unop (yonedaJointlyReflectsLimits _ _ h)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

@[simps]
def Limits.coneOfSectionCompCoyoneda (F : J ⥤ C) (X : Cᵒᵖ)
    (s : (F ⋙ coyoneda.obj X).sections) : Cone F where
  pt := X.unop
  π := compCoyonedaSectionsEquiv F X.unop s

instance coyoneda_preservesLimit (F : J ⥤ C) (X : Cᵒᵖ) :
    PreservesLimit F (coyoneda.obj X) where
  preserves {c} hc := by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨hc.lift (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩), hc.fac _,
      hc.uniq (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩)⟩

variable (J) in

noncomputable instance coyonedaPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (coyoneda.obj X) where

def coyonedaJointlyReflectsLimits (F : J ⥤ C) (c : Cone F)
    (hc : ∀ X : Cᵒᵖ, IsLimit ((coyoneda.obj X).mapCone c)) : IsLimit c where
  lift s := (hc (op s.pt)).lift ((coyoneda.obj (op s.pt)).mapCone s) (𝟙 _)
  fac s j := by simpa using congr_fun ((hc (op s.pt)).fac
    ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 _)
  uniq s m hm := by
    apply (Types.isLimitEquivSections (hc (op s.pt))).injective
    ext j
    dsimp [Types.isLimitEquivSections, Types.sectionOfCone]
    have eq := congr_fun ((hc (op s.pt)).fac ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 _)
    dsimp at eq
    rw [eq, Category.id_comp, ← hm]

noncomputable def Limits.Cone.isLimitCoyonedaEquiv {F : J ⥤ C} (c : Cone F) :
    IsLimit c ≃ ∀ (X : Cᵒᵖ), IsLimit ((coyoneda.obj X).mapCone c) where
  toFun h _ := isLimitOfPreserves _ h
  invFun h := coyonedaJointlyReflectsLimits _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

end

instance yoneda_preservesLimits (X : C) :
    PreservesLimitsOfSize.{t, w} (yoneda.obj X) where

instance coyoneda_preservesLimits (X : Cᵒᵖ) :
    PreservesLimitsOfSize.{t, w} (coyoneda.obj X) where

instance yonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (@yoneda C _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (coyoneda.obj K)
  infer_instance

noncomputable instance coyonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (@coyoneda C _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (yoneda.obj K)
  infer_instance

noncomputable instance yonedaFunctor_reflectsLimits :
    ReflectsLimitsOfSize.{t, w} (@yoneda C _) := inferInstance

noncomputable instance coyonedaFunctor_reflectsLimits :
    ReflectsLimitsOfSize.{t, w} (@coyoneda C _) := inferInstance

namespace Functor

section Representable

variable (F : Cᵒᵖ ⥤ Type v) [F.IsRepresentable] {J : Type*} [Category J]

instance representable_preservesLimit (G : J ⥤ Cᵒᵖ) :
    PreservesLimit G F :=
  preservesLimit_of_natIso _ F.reprW

variable (J) in

instance representable_preservesLimitsOfShape :
    PreservesLimitsOfShape J F where

instance representable_preservesLimits :
    PreservesLimitsOfSize.{t, w} F where

end Representable

section Corepresentable

variable (F : C ⥤ Type v) [F.IsCorepresentable] {J : Type*} [Category J]

instance corepresentable_preservesLimit (G : J ⥤ C) :
    PreservesLimit G F :=
  preservesLimit_of_natIso _ F.coreprW

variable (J) in

instance corepresentable_preservesLimitsOfShape :
    PreservesLimitsOfShape J F where

instance corepresentable_preservesLimits :
    PreservesLimitsOfSize.{t, w} F where

end Corepresentable

end Functor

end CategoryTheory
