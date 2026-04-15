/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/Assoc.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Associativity of pullbacks

This file shows that pullbacks (and pushouts) are associative up to natural isomorphism.

-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section PullbackAssoc

variable {X₁ X₂ X₃ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₁) (f₃ : X₂ ⟶ Y₂)

variable (f₄ : X₃ ⟶ Y₂) [HasPullback f₁ f₂] [HasPullback f₃ f₄]

local notation "Z₁" => pullback f₁ f₂

local notation "Z₂" => pullback f₃ f₄

local notation "g₁" => (pullback.fst _ _ : Z₁ ⟶ X₁)

local notation "g₂" => (pullback.snd _ _ : Z₁ ⟶ X₂)

local notation "g₃" => (pullback.fst _ _ : Z₂ ⟶ X₂)

local notation "g₄" => (pullback.snd _ _ : Z₂ ⟶ X₃)

local notation "W" => pullback (g₂ ≫ f₃) f₄

local notation "W'" => pullback f₁ (g₃ ≫ f₂)

local notation "l₁" => (pullback.fst _ _ : W ⟶ Z₁)

local notation "l₂" =>

  (pullback.lift (pullback.fst _ _ ≫ g₂) (pullback.snd _ _)

      (Eq.trans (Category.assoc _ _ _) pullback.condition) :

    W ⟶ Z₂)

local notation "l₁'" =>

  (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g₃)

      (pullback.condition.trans (Eq.symm (Category.assoc _ _ _))) :

    W' ⟶ Z₁)

local notation "l₂'" => (pullback.snd f₁ (g₃ ≫ f₂))

set_option backward.isDefEq.respectTransparency false in

def pullbackPullbackLeftIsPullback [HasPullback (g₂ ≫ f₃) f₄] : IsLimit (PullbackCone.mk l₁ l₂
    (show l₁ ≫ g₂ = l₂ ≫ g₃ from (pullback.lift_fst _ _ _).symm)) := by
  apply leftSquareIsPullback _ rfl (pullbackIsPullback f₃ f₄)
  simpa [PullbackCone.pasteHoriz] using PullbackCone.mkSelfIsLimit (pullbackIsPullback _ f₄)

def pullbackAssocIsPullback [HasPullback (g₂ ≫ f₃) f₄] :
    IsLimit
      (PullbackCone.mk (l₁ ≫ g₁) l₂
        (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ g₃ ≫ f₂ by
          rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition])) := by
  simpa using pasteVertIsPullback rfl (pullbackIsPullback _ _)
    (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄)

theorem hasPullback_assoc [HasPullback (g₂ ≫ f₃) f₄] : HasPullback f₁ (g₃ ≫ f₂) :=
  ⟨⟨⟨_, pullbackAssocIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in

def pullbackPullbackRightIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit (PullbackCone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃ from pullback.lift_snd _ _ _)) := by
  apply topSquareIsPullback _ rfl (pullbackIsPullback f₁ f₂)
  simpa [PullbackCone.pasteVert] using PullbackCone.mkSelfIsLimit (pullbackIsPullback _ _)

def pullbackAssocSymmIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit
      (PullbackCone.mk l₁' (l₂' ≫ g₄)
        (show l₁' ≫ g₂ ≫ f₃ = (l₂' ≫ g₄) ≫ f₄ by
          rw [pullback.lift_snd_assoc, Category.assoc, Category.assoc, pullback.condition])) := by
  simpa [PullbackCone.pasteHoriz] using pasteHorizIsPullback rfl
    (pullbackIsPullback f₃ f₄) (pullbackPullbackRightIsPullback _ _ _ _)

theorem hasPullback_assoc_symm [HasPullback f₁ (g₃ ≫ f₂)] : HasPullback (g₂ ≫ f₃) f₄ :=
  ⟨⟨⟨_, pullbackAssocSymmIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

noncomputable def pullbackAssoc [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    pullback (pullback.snd _ _ ≫ f₃ : pullback f₁ f₂ ⟶ _) f₄ ≅
      pullback f₁ (pullback.fst _ _ ≫ f₂ : pullback f₃ f₄ ⟶ _) :=
  (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄).conePointUniqueUpToIso
    (pullbackPullbackRightIsPullback f₁ f₂ f₃ f₄)
