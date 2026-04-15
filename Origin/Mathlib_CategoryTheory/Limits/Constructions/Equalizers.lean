/-
Extracted from CategoryTheory/Limits/Constructions/Equalizers.lean
Genuine: 12 of 14 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Constructing equalizers from pullbacks and binary products.

If a category has pullbacks and binary products, then it has equalizers.

TODO: generalize universe
-/

noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v'} D] (G : C ⥤ D)

namespace HasEqualizersOfHasPullbacksAndBinaryProducts

variable [HasBinaryProducts C] [HasPullbacks C]

abbrev constructEqualizer (F : WalkingParallelPair ⥤ C) : C :=
  pullback (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.left))
    (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.right))

abbrev pullbackFst (F : WalkingParallelPair ⥤ C) :
    constructEqualizer F ⟶ F.obj WalkingParallelPair.zero :=
  pullback.fst _ _

set_option backward.isDefEq.respectTransparency false in

theorem pullbackFst_eq_pullback_snd (F : WalkingParallelPair ⥤ C) :
    pullbackFst F = pullback.snd _ _ := by
  convert (eq_whisker pullback.condition Limits.prod.fst :
      (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.zero) = _) <;> simp

set_option backward.isDefEq.respectTransparency false in

abbrev equalizerCone (F : WalkingParallelPair ⥤ C) : Cone F :=
  Cone.ofFork
    (Fork.ofι (pullbackFst F)
      (by
        conv_rhs => rw [pullbackFst_eq_pullback_snd]
        convert (eq_whisker pullback.condition Limits.prod.snd :
          (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.one) = _) using 1 <;> simp))

set_option backward.isDefEq.respectTransparency false in

def equalizerConeIsLimit (F : WalkingParallelPair ⥤ C) : IsLimit (equalizerCone F) where
  lift c := pullback.lift (c.π.app _) (c.π.app _)
  fac := by rintro c (_ | _) <;> simp
  uniq := by
    intro c _ J
    have J0 := J WalkingParallelPair.zero
    apply pullback.hom_ext
    · simpa [limit.lift_π] using J0
    · simp [← J0, pullbackFst_eq_pullback_snd]

end HasEqualizersOfHasPullbacksAndBinaryProducts

open HasEqualizersOfHasPullbacksAndBinaryProducts

theorem hasEqualizers_of_hasPullbacks_and_binary_products [HasBinaryProducts C] [HasPullbacks C] :
    HasEqualizers C :=
  { has_limit := fun F =>
      HasLimit.mk
        { cone := equalizerCone F
          isLimit := equalizerConeIsLimit F } }

attribute [local instance] hasPullback_of_preservesPullback

set_option backward.isDefEq.respectTransparency false in

namespace HasCoequalizersOfHasPushoutsAndBinaryCoproducts

variable [HasBinaryCoproducts C] [HasPushouts C]

abbrev constructCoequalizer (F : WalkingParallelPair ⥤ C) : C :=
  pushout (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.left))
    (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.right))

abbrev pushoutInl (F : WalkingParallelPair ⥤ C) :
    F.obj WalkingParallelPair.one ⟶ constructCoequalizer F :=
  pushout.inl _ _

set_option backward.isDefEq.respectTransparency false in

theorem pushoutInl_eq_pushout_inr (F : WalkingParallelPair ⥤ C) :
    pushoutInl F = pushout.inr _ _ := by
  convert (whisker_eq Limits.coprod.inl pushout.condition :
    (_ : F.obj _ ⟶ constructCoequalizer _) = _) <;> simp

set_option backward.isDefEq.respectTransparency false in

abbrev coequalizerCocone (F : WalkingParallelPair ⥤ C) : Cocone F :=
  Cocone.ofCofork
    (Cofork.ofπ (pushoutInl F) (by
        conv_rhs => rw [pushoutInl_eq_pushout_inr]
        convert (whisker_eq Limits.coprod.inr pushout.condition :
          (_ : F.obj _ ⟶ constructCoequalizer _) = _) using 1 <;> simp))

set_option backward.isDefEq.respectTransparency false in

def coequalizerCoconeIsColimit (F : WalkingParallelPair ⥤ C) : IsColimit (coequalizerCocone F) where
  desc c := pushout.desc (c.ι.app _) (c.ι.app _)
  fac := by rintro c (_ | _) <;> simp
  uniq := by
    intro c m J
    have J1 : pushoutInl F ≫ m = c.ι.app WalkingParallelPair.one := by
      simpa using J WalkingParallelPair.one
    apply pushout.hom_ext
    · rw [colimit.ι_desc]
      exact J1
    · rw [colimit.ι_desc, ← pushoutInl_eq_pushout_inr]
      exact J1

end HasCoequalizersOfHasPushoutsAndBinaryCoproducts

open HasCoequalizersOfHasPushoutsAndBinaryCoproducts

theorem hasCoequalizers_of_hasPushouts_and_binary_coproducts [HasBinaryCoproducts C]
    [HasPushouts C] : HasCoequalizers C :=
  {
    has_colimit := fun F =>
      HasColimit.mk
        { cocone := coequalizerCocone F
          isColimit := coequalizerCoconeIsColimit F } }

attribute [local instance] hasPushout_of_preservesPushout

set_option backward.isDefEq.respectTransparency false in

end CategoryTheory.Limits
