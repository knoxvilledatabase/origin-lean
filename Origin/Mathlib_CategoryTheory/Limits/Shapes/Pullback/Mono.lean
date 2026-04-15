/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/Mono.lean
Genuine: 9 of 18 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Pullbacks and monomorphisms

This file provides some results about interactions between pullbacks and monomorphisms, as well as
the dual statements between pushouts and epimorphisms.

## Main results
* Monomorphisms are stable under pullback. This is available using the `PullbackCone` API as
  `mono_fst_of_is_pullback_of_mono` and `mono_snd_of_is_pullback_of_mono`, and using the `pullback`
  API as `pullback.fst_of_mono` and `pullback.snd_of_mono`.

* A pullback cone is a limit iff its composition with a monomorphism is a limit. This is available
  as `IsLimitOfCompMono` and `pullbackIsPullbackOfCompMono` respectively.

* Monomorphisms admit kernel pairs, this is `has_kernel_pair_of_mono`.

The dual notions for pushouts are also available.
-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom PullbackCone

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

section Monomorphisms

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

theorem mono_snd_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono f] :
    Mono t.snd := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht ?_ i⟩
  rw [← cancel_mono f, Category.assoc, Category.assoc, condition]
  apply reassoc_of% i

theorem mono_fst_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono g] :
    Mono t.fst := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht i ?_⟩
  rw [← cancel_mono g, Category.assoc, Category.assoc, ← condition]
  apply reassoc_of% i

def isLimitMkIdId (f : X ⟶ Y) [Mono f] : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f) :=
  IsLimit.mk _ (fun s => s.fst) (fun _ => Category.comp_id _)
    (fun s => by rw [← cancel_mono f, Category.comp_id, s.condition]) fun s m m₁ _ => by
    simpa using m₁

theorem mono_of_isLimitMkIdId (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) :
    Mono f :=
  ⟨fun {Z} g h eq => by
    rcases PullbackCone.IsLimit.lift' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

set_option backward.isDefEq.respectTransparency false in

def isLimitOfFactors (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [Mono h] (x : X ⟶ W) (y : Y ⟶ W)
    (hxh : x ≫ h = f) (hyh : y ≫ h = g) (s : PullbackCone f g) (hs : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ x = s.snd ≫ y from
          (cancel_mono h).1 <| by simp only [Category.assoc, hxh, hyh, s.condition])) :=
  PullbackCone.isLimitAux' _ fun t =>
    have : fst t ≫ x ≫ h = snd t ≫ y ≫ h := by  -- Porting note: reassoc workaround
      rw [← Category.assoc, ← Category.assoc]
      apply congrArg (· ≫ h) t.condition
    ⟨hs.lift (PullbackCone.mk t.fst t.snd <| by rw [← hxh, ← hyh, this]),
      ⟨hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right, fun hr hr' => by
        apply PullbackCone.IsLimit.hom_ext hs <;>
              simp only [PullbackCone.mk_fst, PullbackCone.mk_snd] at hr hr' ⊢ <;>
            simp only [hr, hr'] <;>
          symm
        exacts [hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right]⟩⟩

def isLimitOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] (s : PullbackCone f g)
    (H : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ f ≫ i = s.snd ≫ g ≫ i by
          rw [← Category.assoc, ← Category.assoc, s.condition])) := by
  apply PullbackCone.isLimitAux'
  intro s
  rcases PullbackCone.IsLimit.lift' H s.fst s.snd
      ((cancel_mono i).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PullbackCone.IsLimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) :)

end PullbackCone

end Monomorphisms

-- INSTANCE (free from Core): pullback.fst_of_mono

-- INSTANCE (free from Core): pullback.snd_of_mono

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): mono_pullback_to_prod

noncomputable def pullbackIsPullbackOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i]
    [HasPullback f g] : IsLimit (PullbackCone.mk (pullback.fst f g) (pullback.snd f g)
      -- Porting note: following used to be _
      (show (pullback.fst f g) ≫ f ≫ i = (pullback.snd f g) ≫ g ≫ i by
        simp only [← Category.assoc]; rw [cancel_mono]; apply pullback.condition)) :=
  PullbackCone.isLimitOfCompMono f g i _ (limit.isLimit (cospan f g))

-- INSTANCE (free from Core): hasPullback_of_comp_mono

attribute [local instance] hasPullback_of_left_iso

variable (f : X ⟶ Z) (i : Z ⟶ W) [Mono i]

-- INSTANCE (free from Core): hasPullback_of_right_factors_mono

-- INSTANCE (free from Core): pullback_snd_iso_of_right_factors_mono

attribute [local instance] hasPullback_of_right_iso

-- INSTANCE (free from Core): hasPullback_of_left_factors_mono

-- INSTANCE (free from Core): pullback_snd_iso_of_left_factors_mono

end

open WalkingCospan

variable (f : X ⟶ Y) [Mono f]

-- INSTANCE (free from Core): has_kernel_pair_of_mono

theorem PullbackCone.fst_eq_snd_of_mono_eq {f : X ⟶ Y} [Mono f] (t : PullbackCone f f) :
    t.fst = t.snd :=
  (cancel_mono f).1 t.condition

theorem fst_eq_snd_of_mono_eq : pullback.fst f f = pullback.snd f f :=
  PullbackCone.fst_eq_snd_of_mono_eq (getLimitCone (cospan f f)).cone
