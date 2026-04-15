/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/Pasting.lean
Genuine: 19 of 20 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Pasting lemma

This file proves the pasting lemma for pullbacks. That is, given the following diagram:
```
  X₁ - f₁ -> X₂ - f₂ -> X₃
  |          |          |
  i₁         i₂         i₃
  ∨          ∨          ∨
  Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
if the right square is a pullback, then the left square is a pullback iff the big square is a
pullback.

## Main results
* `pasteHorizIsPullback` shows that the big square is a pullback if both the small squares are.
* `leftSquareIsPullback` shows that the left square is a pullback if the other two are.
* `pullbackRightPullbackFstIso` shows, using the `pullback` API, that
  `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y`.
* `pullbackLeftPullbackSndIso` shows, using the `pullback` API, that
  `(X ×[Z] Y) ×[Y] W ≅ X ×[Z] W`.

-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section PasteLemma

section PastePullbackHoriz

variable {X₃ Y₁ Y₂ Y₃ : C} {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {i₃ : X₃ ⟶ Y₃}

abbrev PullbackCone.pasteHoriz
    (t₂ : PullbackCone g₂ i₃) {i₂ : t₂.pt ⟶ Y₂} (t₁ : PullbackCone g₁ i₂) (hi₂ : i₂ = t₂.fst) :
    PullbackCone (g₁ ≫ g₂) i₃ :=
  PullbackCone.mk t₁.fst (t₁.snd ≫ t₂.snd)
    (by rw [reassoc_of% t₁.condition, Category.assoc, ← t₂.condition, ← hi₂])

variable (t₂ : PullbackCone g₂ i₃) {i₂ : t₂.pt ⟶ Y₂} (t₁ : PullbackCone g₁ i₂) (hi₂ : i₂ = t₂.fst)

local notation "f₂" => t₂.snd

local notation "X₁" => t₁.pt

local notation "i₁" => t₁.fst

local notation "f₁" => t₁.snd

variable {t₁} {t₂}

def pasteHorizIsPullback (H : IsLimit t₂) (H' : IsLimit t₁) : IsLimit (t₂.pasteHoriz t₁ hi₂) := by
  apply PullbackCone.isLimitAux'
  intro s
  -- Obtain the lift from lifting from both the small squares consecutively.
  obtain ⟨l₂, hl₂, hl₂'⟩ := PullbackCone.IsLimit.lift' H (s.fst ≫ g₁) s.snd
    (by rw [← s.condition, Category.assoc])
  obtain ⟨l₁, hl₁, hl₁'⟩ := PullbackCone.IsLimit.lift' H' s.fst l₂ (by rw [← hl₂, hi₂])
  refine ⟨l₁, hl₁, by simp [reassoc_of% hl₁', hl₂'], ?_⟩
  -- Uniqueness also follows from the universal property of both the small squares.
  intro m hm₁ hm₂
  apply PullbackCone.IsLimit.hom_ext H' (by simpa [hl₁] using hm₁)
  apply PullbackCone.IsLimit.hom_ext H
  · dsimp at hm₁
    rw [Category.assoc, ← hi₂, ← t₁.condition, reassoc_of% hm₁, hl₁', hi₂, hl₂]
  · simpa [hl₁', hl₂'] using hm₂

variable (t₁)

def leftSquareIsPullback (H : IsLimit t₂) (H' : IsLimit (t₂.pasteHoriz t₁ hi₂)) : IsLimit t₁ := by
  apply PullbackCone.isLimitAux'
  intro s
  -- Obtain the induced morphism from the universal property of the big square
  obtain ⟨l, hl, hl'⟩ := PullbackCone.IsLimit.lift' H' s.fst (s.snd ≫ f₂)
    (by rw [Category.assoc, ← t₂.condition, reassoc_of% s.condition, ← hi₂])
  refine ⟨l, hl, ?_, ?_⟩
  -- To check that `l` is compatible with the projections, we use the universal property of `t₂`
  · apply PullbackCone.IsLimit.hom_ext H
    · simp [← s.condition, ← hl, ← t₁.condition, ← hi₂]
    · simpa using hl'
  -- Uniqueness of the lift follows from the universal property of the big square
  · intro m hm₁ hm₂
    apply PullbackCone.IsLimit.hom_ext H'
    · simpa [hm₁] using hl.symm
    · simpa [← hm₂] using hl'.symm

def pasteHorizIsPullbackEquiv (H : IsLimit t₂) : IsLimit (t₂.pasteHoriz t₁ hi₂) ≃ IsLimit t₁ where
  toFun H' := leftSquareIsPullback t₁ _ H H'
  invFun H' := pasteHorizIsPullback _ H H'
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PastePullbackHoriz

section PastePullbackVert

variable {X₁ X₂ X₃ Y₁ : C} {f₁ : X₂ ⟶ X₁} {f₂ : X₃ ⟶ X₂} {i₁ : Y₁ ⟶ X₁}

abbrev PullbackCone.pasteVert
    (t₁ : PullbackCone i₁ f₁) {i₂ : t₁.pt ⟶ X₂} (t₂ : PullbackCone i₂ f₂) (hi₂ : i₂ = t₁.snd) :
    PullbackCone i₁ (f₂ ≫ f₁) :=
  PullbackCone.mk (t₂.fst ≫ t₁.fst) t₂.snd
    (by rw [← reassoc_of% t₂.condition, Category.assoc, t₁.condition, ← hi₂])

variable (t₁ : PullbackCone i₁ f₁) {i₂ : t₁.pt ⟶ X₂} (t₂ : PullbackCone i₂ f₂) (hi₂ : i₂ = t₁.snd)

local notation "Y₂" => t₁.pt

local notation "g₁" => t₁.fst

local notation "i₂" => t₁.snd

local notation "Y₃" => t₂.pt

local notation "g₂" => t₂.fst

local notation "i₃" => t₂.snd

def PullbackCone.pasteVertFlip : (t₁.pasteVert t₂ hi₂).flip ≅ (t₁.flip.pasteHoriz t₂.flip hi₂) :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

variable {t₁} {t₂}

def pasteVertIsPullback (H₁ : IsLimit t₁) (H₂ : IsLimit t₂) : IsLimit (t₁.pasteVert t₂ hi₂) := by
  apply PullbackCone.isLimitOfFlip <| IsLimit.ofIsoLimit _ (t₁.pasteVertFlip t₂ hi₂).symm
  exact pasteHorizIsPullback hi₂ (PullbackCone.flipIsLimit H₁) (PullbackCone.flipIsLimit H₂)

variable (t₂)

def topSquareIsPullback (H₁ : IsLimit t₁) (H₂ : IsLimit (t₁.pasteVert t₂ hi₂)) : IsLimit t₂ :=
  PullbackCone.isLimitOfFlip
    (leftSquareIsPullback _ hi₂ (PullbackCone.flipIsLimit H₁) (PullbackCone.flipIsLimit H₂))

def pasteVertIsPullbackEquiv (H : IsLimit t₁) : IsLimit (t₁.pasteVert t₂ hi₂) ≃ IsLimit t₂ where
  toFun H' := topSquareIsPullback t₂ _ H H'
  invFun H' := pasteVertIsPullback _ H H'
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PastePullbackVert

section PastePushoutHoriz

variable {X₁ X₂ X₃ Y₁ : C} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {i₁ : X₁ ⟶ Y₁}

abbrev PushoutCocone.pasteHoriz
    (t₁ : PushoutCocone i₁ f₁) {i₂ : X₂ ⟶ t₁.pt} (t₂ : PushoutCocone i₂ f₂) (hi₂ : i₂ = t₁.inr) :
    PushoutCocone i₁ (f₁ ≫ f₂) :=
  PushoutCocone.mk (t₁.inl ≫ t₂.inl) t₂.inr
    (by rw [reassoc_of% t₁.condition, Category.assoc, ← t₂.condition, ← hi₂])

variable (t₁ : PushoutCocone i₁ f₁) {i₂ : X₂ ⟶ t₁.pt} (t₂ : PushoutCocone i₂ f₂) (hi₂ : i₂ = t₁.inr)

local notation "Y₂" => t₁.pt

local notation "g₁" => t₁.inl

local notation "i₂" => t₁.inr

local notation "Y₃" => t₂.pt

local notation "g₂" => t₂.inl

local notation "i₃" => t₂.inr

variable {t₁} {t₂}

def pasteHorizIsPushout (H : IsColimit t₁) (H' : IsColimit t₂) :
    IsColimit (t₁.pasteHoriz t₂ hi₂) := by
  apply PushoutCocone.isColimitAux'
  intro s
  -- Obtain the induced map from descending from both the small squares consecutively.
  obtain ⟨l₁, hl₁, hl₁'⟩ := PushoutCocone.IsColimit.desc' H s.inl (f₂ ≫ s.inr)
    (by rw [s.condition, Category.assoc])
  obtain ⟨l₂, hl₂, hl₂'⟩ := PushoutCocone.IsColimit.desc' H' l₁ s.inr (by rw [← hl₁', hi₂])
  refine ⟨l₂, by simp [hl₂, hl₁], hl₂', ?_⟩
  -- Uniqueness also follows from the universal property of both the small squares.
  intro m hm₁ hm₂
  apply PushoutCocone.IsColimit.hom_ext H' _ (by simpa [hl₂'] using hm₂)
  simp only [PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, Category.assoc] at hm₁ hm₂
  apply PushoutCocone.IsColimit.hom_ext H
  · rw [hm₁, ← hl₁, hl₂]
  · rw [← hi₂, reassoc_of% t₂.condition, reassoc_of% t₂.condition, hm₂, hl₂']

variable (t₂)

def rightSquareIsPushout (H : IsColimit t₁) (H' : IsColimit (t₁.pasteHoriz t₂ hi₂)) :
    IsColimit t₂ := by
  apply PushoutCocone.isColimitAux'
  intro s
  -- Obtain the induced morphism from the universal property of the big square
  obtain ⟨l, hl, hl'⟩ := PushoutCocone.IsColimit.desc' H' (g₁ ≫ s.inl) s.inr
    (by rw [reassoc_of% t₁.condition, ← hi₂, s.condition, Category.assoc])
  refine ⟨l, ?_, hl', ?_⟩
  -- To check that `l` is compatible with the projections, we use the universal property of `t₁`
  · simp only [PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, Category.assoc] at hl hl'
    apply PushoutCocone.IsColimit.hom_ext H hl
    rw [← Category.assoc, ← hi₂, t₂.condition, s.condition, Category.assoc, hl']
  -- Uniqueness of the lift follows from the universal property of the big square
  · intro m hm₁ hm₂
    apply PushoutCocone.IsColimit.hom_ext H'
    · simpa [← hm₁] using hl.symm
    · simpa [← hm₂] using hl'.symm

def pasteHorizIsPushoutEquiv (H : IsColimit t₁) :
    IsColimit (t₁.pasteHoriz t₂ hi₂) ≃ IsColimit t₂ where
  toFun H' := rightSquareIsPushout t₂ _ H H'
  invFun H' := pasteHorizIsPushout _ H H'
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PastePushoutHoriz

section PastePushoutVert

variable {Y₃ Y₂ Y₁ X₃ : C} {g₂ : Y₃ ⟶ Y₂} {g₁ : Y₂ ⟶ Y₁} {i₃ : Y₃ ⟶ X₃}

variable (t₁ : PushoutCocone g₂ i₃) {i₂ : Y₂ ⟶ t₁.pt} (t₂ : PushoutCocone g₁ i₂)
  (hi₂ : i₂ = t₁.inl)

abbrev PushoutCocone.pasteVert
    (t₁ : PushoutCocone g₂ i₃) {i₂ : Y₂ ⟶ t₁.pt} (t₂ : PushoutCocone g₁ i₂) (hi₂ : i₂ = t₁.inl) :
    PushoutCocone (g₂ ≫ g₁) i₃ :=
  PushoutCocone.mk t₂.inl (t₁.inr ≫ t₂.inr)
    (by rw [← reassoc_of% t₁.condition, Category.assoc, t₂.condition, ← hi₂])

local notation "X₂" => t₁.pt

local notation "f₂" => t₁.inr

local notation "i₂" => t₁.inl

local notation "X₁" => t₂.pt

local notation "f₁" => t₂.inr

local notation "i₁" => t₂.inl

def PushoutCocone.pasteVertFlip : (t₁.pasteVert t₂ hi₂).flip ≅ (t₁.flip.pasteHoriz t₂.flip hi₂) :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

variable {t₁} {t₂}

def pasteVertIsPushout (H₁ : IsColimit t₁) (H₂ : IsColimit t₂) :
    IsColimit (t₁.pasteVert t₂ hi₂) := by
  apply PushoutCocone.isColimitOfFlip <| IsColimit.ofIsoColimit _ (t₁.pasteVertFlip t₂ hi₂).symm
  exact pasteHorizIsPushout hi₂ (PushoutCocone.flipIsColimit H₁) (PushoutCocone.flipIsColimit H₂)

variable (t₂)

def botSquareIsPushout (H₁ : IsColimit t₁) (H₂ : IsColimit (t₁.pasteVert t₂ hi₂)) : IsColimit t₂ :=
  PushoutCocone.isColimitOfFlip
    (rightSquareIsPushout _ hi₂ (PushoutCocone.flipIsColimit H₁) (PushoutCocone.flipIsColimit H₂))

def pasteVertIsPushoutEquiv (H : IsColimit t₁) :
    IsColimit (t₁.pasteVert t₂ hi₂) ≃ IsColimit t₂ where
  toFun H' := botSquareIsPushout t₂ _ H H'
  invFun H' := pasteVertIsPushout _ H H'
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PastePushoutVert

end PasteLemma

variable {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : W ⟶ X)

variable [HasPullback f g] [HasPullback f' (pullback.fst f g)]

-- INSTANCE (free from Core): hasPullbackHorizPaste

noncomputable def pullbackRightPullbackFstIso :
    pullback f' (pullback.fst f g) ≅ pullback (f' ≫ f) g :=
  IsLimit.conePointUniqueUpToIso
    (pasteHorizIsPullback rfl (pullback.isLimit f g) (pullback.isLimit f' (pullback.fst f g)))
    (pullback.isLimit (f' ≫ f) g)
