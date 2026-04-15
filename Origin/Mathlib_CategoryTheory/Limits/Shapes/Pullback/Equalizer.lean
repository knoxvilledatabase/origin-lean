/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/Equalizer.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equalizers as pullbacks of products

Also see `CategoryTheory.Limits.Constructions.Equalizers` for very similar results.

-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y : C} (f g : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in

lemma isPullback_equalizer_prod [HasEqualizer f g] [HasBinaryProduct Y Y] :
    IsPullback (equalizer.ι f g) (equalizer.ι f g ≫ f) (prod.lift f g) (prod.lift (𝟙 _) (𝟙 _)) := by
  refine ⟨⟨by ext <;> simp [equalizer.condition f g]⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · refine fun s ↦ equalizer.lift s.fst ?_
    have H₁ : s.fst ≫ f = s.snd := by simpa using congr($s.condition ≫ prod.fst)
    have H₂ : s.fst ≫ g = s.snd := by simpa using congr($s.condition ≫ prod.snd)
    exact H₁.trans H₂.symm
  · exact fun s ↦ by simp
  · exact fun s ↦ by simpa using congr($s.condition ≫ prod.fst)
  · exact fun s m hm _ ↦ by ext; simp [*]

set_option backward.isDefEq.respectTransparency false in

lemma isPushout_coequalizer_coprod [HasCoequalizer f g] [HasBinaryCoproduct X X] :
    IsPushout (coprod.desc f g) (coprod.desc (𝟙 _) (𝟙 _))
      (coequalizer.π f g) (f ≫ coequalizer.π f g) := by
  refine ⟨⟨by ext <;> simp [coequalizer.condition f g]⟩, ⟨PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · refine fun s ↦ coequalizer.desc s.inl ?_
    have H₁ : f ≫ s.inl = s.inr := by simpa using congr(coprod.inl ≫ $s.condition)
    have H₂ : g ≫ s.inl = s.inr := by simpa using congr(coprod.inr ≫ $s.condition)
    exact H₁.trans H₂.symm
  · exact fun s ↦ by simp
  · exact fun s ↦ by simpa using congr(coprod.inl ≫ $s.condition)
  · exact fun s m hm _ ↦ by ext; simp [*]

variable [HasEqualizers C] [HasPullbacks C] {X Y S T : C}

set_option backward.isDefEq.respectTransparency false in

noncomputable def equalizerPullbackMapIso {f g : X ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (hf : f ≫ t = s) (hg : g ≫ t = s) (v : T ⟶ S) :
    equalizer
      (pullback.map s v t v f (𝟙 T) (𝟙 S) (by simp [hf]) (by simp))
      (pullback.map s v t v g (𝟙 T) (𝟙 S) (by simp [hg]) (by simp)) ≅
    pullback (equalizer.ι f g) (pullback.fst s v) :=
  letI lhs := pullback.map s v t v f (𝟙 T) (𝟙 S) (by simp [hf]) (by simp)
  letI rhs := pullback.map s v t v g (𝟙 T) (𝟙 S) (by simp [hg]) (by simp)
  haveI hl : pullback.fst s v ≫ f = lhs ≫ pullback.fst _ _ := by simp [lhs]
  haveI hr : pullback.fst s v ≫ g = rhs ≫ pullback.fst _ _ := by simp [rhs]
  letI e : equalizer lhs rhs ≅ pullback (equalizer.ι f g) (pullback.fst s v) :=
    { hom := pullback.lift
        (equalizer.lift (equalizer.ι _ _ ≫ pullback.fst _ _) (by
          simp [hl, hr, equalizer.condition_assoc lhs rhs]))
        (pullback.lift (equalizer.ι _ _ ≫ pullback.fst _ _)
          (equalizer.ι _ _ ≫ pullback.snd _ _) (by simp [pullback.condition]))
        (by simp)
      inv := equalizer.lift
        (pullback.map _ _ _ _ (equalizer.ι _ _) (pullback.snd _ _) s rfl
          (by simp [pullback.condition]))
        (by ext <;> simp [lhs, rhs, equalizer.condition f g])
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp [pullback.condition] }
  e

variable {f g : X ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (hf : f ≫ t = s) (hg : g ≫ t = s) (v : T ⟶ S)

set_option backward.isDefEq.respectTransparency false in
