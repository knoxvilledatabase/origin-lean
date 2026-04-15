/-
Extracted from CategoryTheory/Limits/MorphismProperty.lean
Genuine: 8 of 13 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# (Co)limits in subcategories of comma categories defined by morphism properties

-/

namespace CategoryTheory

open Limits MorphismProperty.Comma

variable {T : Type*} [Category T] (P : MorphismProperty T)

namespace MorphismProperty.Comma

variable {A B J : Type*} [Category A] [Category B] [Category J] {L : A ⥤ T} {R : B ⥤ T}

variable (D : J ⥤ P.Comma L R ⊤ ⊤)

noncomputable def forgetCreatesLimitOfClosed
    (h : ClosedUnderLimitsOfShape J (fun f : Comma L R ↦ P f.hom))
    [HasLimit (D ⋙ forget L R P ⊤ ⊤)] :
    CreatesLimit D (forget L R P ⊤ ⊤) :=
  createsLimitOfFullyFaithfulOfIso
    (⟨limit (D ⋙ forget L R P ⊤ ⊤), h.limit fun j ↦ (D.obj j).prop⟩)
    (Iso.refl _)

noncomputable def forgetCreatesLimitsOfShapeOfClosed [HasLimitsOfShape J (Comma L R)]
    (h : ClosedUnderLimitsOfShape J (fun f : Comma L R ↦ P f.hom)) :
    CreatesLimitsOfShape J (forget L R P ⊤ ⊤) where
  CreatesLimit := forgetCreatesLimitOfClosed _ _ h

lemma hasLimit_of_closedUnderLimitsOfShape
    (h : ClosedUnderLimitsOfShape J (fun f : Comma L R ↦ P f.hom))
    [HasLimit (D ⋙ forget L R P ⊤ ⊤)] :
    HasLimit D :=
  haveI : CreatesLimit D (forget L R P ⊤ ⊤) := forgetCreatesLimitOfClosed _ D h
  hasLimit_of_created D (forget L R P ⊤ ⊤)

lemma hasLimitsOfShape_of_closedUnderLimitsOfShape [HasLimitsOfShape J (Comma L R)]
    (h : ClosedUnderLimitsOfShape J (fun f : Comma L R ↦ P f.hom)) :
    HasLimitsOfShape J (P.Comma L R ⊤ ⊤) where
  has_limit _ := hasLimit_of_closedUnderLimitsOfShape _ _ h

end MorphismProperty.Comma

section

variable {A : Type*} [Category A] {L : A ⥤ T}

lemma CostructuredArrow.closedUnderLimitsOfShape_discrete_empty [L.Faithful] [L.Full] {Y : A}
    [P.ContainsIdentities] [P.RespectsIso] :
    ClosedUnderLimitsOfShape (Discrete PEmpty.{1})
      (fun f : CostructuredArrow L (L.obj Y) ↦ P f.hom) := by
  rintro D c hc -
  have : D = Functor.empty _ := Functor.empty_ext' _ _
  subst this
  let e : c.pt ≅ CostructuredArrow.mk (𝟙 (L.obj Y)) :=
    hc.conePointUniqueUpToIso CostructuredArrow.mkIdTerminal
  rw [P.costructuredArrow_iso_iff e]
  simpa using P.id_mem (L.obj Y)

end

section

variable {X : T}

lemma Over.closedUnderLimitsOfShape_discrete_empty [P.ContainsIdentities] [P.RespectsIso] :
    ClosedUnderLimitsOfShape (Discrete PEmpty.{1}) (fun f : Over X ↦ P f.hom) :=
  CostructuredArrow.closedUnderLimitsOfShape_discrete_empty P

lemma Over.closedUnderLimitsOfShape_pullback [HasPullbacks T]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    ClosedUnderLimitsOfShape WalkingCospan (fun f : Over X ↦ P f.hom) := by
  intro D c hc hf
  have h : IsPullback (c.π.app .left).left (c.π.app .right).left (D.map WalkingCospan.Hom.inl).left
        (D.map WalkingCospan.Hom.inr).left := IsPullback.of_isLimit_cone <|
    Limits.isLimitOfPreserves (CategoryTheory.Over.forget X) hc
  rw [show c.pt.hom = (c.π.app .left).left ≫ (D.obj .left).hom by simp]
  apply P.comp_mem _ _ (P.of_isPullback h.flip ?_) (hf _)
  exact P.of_postcomp _ (D.obj WalkingCospan.one).hom (hf .one) (by simpa using hf .right)

end

namespace MorphismProperty.Over

variable (X : T)

noncomputable instance [P.ContainsIdentities] [P.RespectsIso] :
    CreatesLimitsOfShape (Discrete PEmpty.{1}) (Over.forget P ⊤ X) :=
  haveI : HasLimitsOfShape (Discrete PEmpty.{1}) (Comma (𝟭 T) (Functor.fromPUnit X)) := by
    show HasLimitsOfShape _ (Over X)
    infer_instance
  forgetCreatesLimitsOfShapeOfClosed P
    (Over.closedUnderLimitsOfShape_discrete_empty _)

variable {X} in

instance [P.ContainsIdentities] (Y : P.Over ⊤ X) :
    Unique (Y ⟶ Over.mk ⊤ (𝟙 X) (P.id_mem X)) where
  default := Over.homMk Y.hom
  uniq a := by
    ext
    · simp only [mk_left, Hom.hom_left, homMk_hom, Over.homMk_left]
      rw [← Over.w a]
      simp only [mk_left, Functor.const_obj_obj, Hom.hom_left, mk_hom, Category.comp_id]

def mkIdTerminal [P.ContainsIdentities] :
    IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_mem X)) :=
  IsTerminal.ofUnique _

instance [P.ContainsIdentities] : HasTerminal (P.Over ⊤ X) :=
  let h : IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_mem X)) := Over.mkIdTerminal P X
  h.hasTerminal

noncomputable instance createsLimitsOfShape_walkingCospan [HasPullbacks T]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    CreatesLimitsOfShape WalkingCospan (Over.forget P ⊤ X) :=
  haveI : HasLimitsOfShape WalkingCospan (Comma (𝟭 T) (Functor.fromPUnit X)) :=
    inferInstanceAs <| HasLimitsOfShape WalkingCospan (Over X)
  forgetCreatesLimitsOfShapeOfClosed P
    (Over.closedUnderLimitsOfShape_pullback P)

instance (priority := 900) hasPullbacks [HasPullbacks T] [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] : HasPullbacks (P.Over ⊤ X) :=
  haveI : HasLimitsOfShape WalkingCospan (Comma (𝟭 T) (Functor.fromPUnit X)) :=
    inferInstanceAs <| HasLimitsOfShape WalkingCospan (Over X)
  hasLimitsOfShape_of_closedUnderLimitsOfShape P
    (Over.closedUnderLimitsOfShape_pullback P)

end MorphismProperty.Over

end CategoryTheory
