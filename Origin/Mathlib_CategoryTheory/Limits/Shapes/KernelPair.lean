/-
Extracted from CategoryTheory/Limits/Shapes/KernelPair.lean
Genuine: 14 of 16 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Kernel pairs

This file defines what it means for a parallel pair of morphisms `a b : R ⟶ X` to be the kernel pair
for a morphism `f`.
Some properties of kernel pairs are given, namely allowing one to transfer between
the kernel pair of `f₁ ≫ f₂` to the kernel pair of `f₁`.
It is also proved that if `f` is a coequalizer of some pair, and `a`,`b` is a kernel pair for `f`
then it is a coequalizer of `a`,`b`.

## Implementation

The definition is essentially just a wrapper for `IsLimit (PullbackCone.mk _ _ _)`, but the
constructions given here are useful, yet awkward to present in that language, so a basic API
is developed here.

## TODO

- Internal equivalence relations (or congruences) and the fact that every kernel pair induces one,
  and the converse in an effective regular category (WIP by b-mehta).

-/

universe v u u₂

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {R X Y Z : C} (f : X ⟶ Y) (a b : R ⟶ X)

abbrev IsKernelPair :=
  IsPullback a b f f

namespace IsKernelPair

instance : Subsingleton (IsKernelPair f a b) :=
  ⟨fun P Q => by
    cases P
    cases Q
    congr ⟩

theorem id_of_mono [Mono f] : IsKernelPair f (𝟙 _) (𝟙 _) :=
  ⟨⟨rfl⟩, ⟨PullbackCone.isLimitMkIdId _⟩⟩

instance [Mono f] : Inhabited (IsKernelPair f (𝟙 _) (𝟙 _)) :=
  ⟨id_of_mono f⟩

variable {f a b}

noncomputable def lift {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    S ⟶ R :=
  PullbackCone.IsLimit.lift k.isLimit _ _ w

@[reassoc (attr := simp)]
lemma lift_fst {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    k.lift p q w ≫ a = p :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma lift_snd {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    k.lift p q w ≫ b = q :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

noncomputable def lift' {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    { t : S ⟶ R // t ≫ a = p ∧ t ≫ b = q } :=
  ⟨k.lift p q w, by simp⟩

theorem cancel_right {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁)
    (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  { w := comm
    isLimit' :=
      ⟨PullbackCone.isLimitAux' _ fun s => by
        let s' : PullbackCone (f₁ ≫ f₂) (f₁ ≫ f₂) :=
          PullbackCone.mk s.fst s.snd (s.condition_assoc _)
        refine ⟨big_k.isLimit.lift s', big_k.isLimit.fac _ WalkingCospan.left,
          big_k.isLimit.fac _ WalkingCospan.right, fun m₁ m₂ => ?_⟩
        apply big_k.isLimit.hom_ext
        refine (PullbackCone.mk a b ?_ : PullbackCone (f₁ ≫ f₂) _).equalizer_ext ?_ ?_
        · apply reassoc_of% comm
        · apply m₁.trans (big_k.isLimit.fac s' WalkingCospan.left).symm
        · apply m₂.trans (big_k.isLimit.fac s' WalkingCospan.right).symm⟩ }

theorem cancel_right_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂]
    (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  cancel_right (by rw [← cancel_mono f₂, assoc, assoc, big_k.w]) big_k

theorem comp_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂] (small_k : IsKernelPair f₁ a b) :
    IsKernelPair (f₁ ≫ f₂) a b :=
  { w := by rw [small_k.w_assoc]
    isLimit' := ⟨by
      refine PullbackCone.isLimitAux _
        (fun s => small_k.lift s.fst s.snd (by rw [← cancel_mono f₂, assoc, s.condition, assoc]))
        (by simp) (by simp) ?_
      intro s m hm
      apply small_k.isLimit.hom_ext
      apply PullbackCone.equalizer_ext small_k.cone _ _
      · exact (hm WalkingCospan.left).trans (by simp)
      · exact (hm WalkingCospan.right).trans (by simp)⟩ }

def toCoequalizer (k : IsKernelPair f a b) [r : RegularEpi f] : IsColimit (Cofork.ofπ f k.w) := by
  let t := k.isLimit.lift (PullbackCone.mk _ _ r.w)
  have ht : t ≫ a = r.left := k.isLimit.fac _ WalkingCospan.left
  have kt : t ≫ b = r.right := k.isLimit.fac _ WalkingCospan.right
  refine Cofork.IsColimit.mk _
    (fun s => Cofork.IsColimit.desc r.isColimit s.π
      (by rw [← ht, assoc, s.condition, reassoc_of% kt]))
    (fun s => ?_) (fun s m w => ?_)
  · apply Cofork.IsColimit.π_desc' r.isColimit
  · apply Cofork.IsColimit.hom_ext r.isColimit
    exact w.trans (Cofork.IsColimit.π_desc' r.isColimit _ _).symm

protected theorem pullback {X Y Z A : C} {g : Y ⟶ Z} {a₁ a₂ : A ⟶ Y} (h : IsKernelPair g a₁ a₂)
    (f : X ⟶ Z) [HasPullback f g] [HasPullback f (a₁ ≫ g)] :
    IsKernelPair (pullback.fst f g)
      (pullback.map f _ f _ (𝟙 X) a₁ (𝟙 Z) (by simp) <| Category.comp_id _)
      (pullback.map _ _ _ _ (𝟙 X) a₂ (𝟙 Z) (by simp) <| (Category.comp_id _).trans h.1.1) := by
  refine ⟨⟨by rw [pullback.lift_fst, pullback.lift_fst]⟩, ⟨PullbackCone.isLimitAux _
    (fun s => pullback.lift (s.fst ≫ pullback.fst _ _)
      (h.lift (s.fst ≫ pullback.snd _ _) (s.snd ≫ pullback.snd _ _) ?_ ) ?_) (fun s => ?_)
        (fun s => ?_) (fun s m hm => ?_)⟩⟩
  · simp_rw [Category.assoc, ← pullback.condition, ← Category.assoc, s.condition]
  · simp only [assoc, lift_fst_assoc, pullback.condition]
  · ext <;> simp
  · ext
    · simp [s.condition]
    · simp
  · #adaptation_note /-- nightly-2024-04-01
    This `symm` (or the following ones that undo it) wasn't previously necessary. -/
    symm
    apply pullback.hom_ext
    · symm
      simpa using hm WalkingCospan.left =≫ pullback.fst f g
    · symm
      apply PullbackCone.IsLimit.hom_ext h.isLimit
      · simpa using hm WalkingCospan.left =≫ pullback.snd f g
      · simpa using hm WalkingCospan.right =≫ pullback.snd f g

theorem mono_of_isIso_fst (h : IsKernelPair f a b) [IsIso a] : Mono f := by
  obtain ⟨l, h₁, h₂⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit (𝟙 _) (𝟙 _) (by simp [h.w])
  rw [IsPullback.cone_fst, ← IsIso.eq_comp_inv, Category.id_comp] at h₁
  rw [h₁, IsIso.inv_comp_eq, Category.comp_id] at h₂
  constructor
  intro Z g₁ g₂ e
  obtain ⟨l', rfl, rfl⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit _ _ e
  rw [IsPullback.cone_fst, h₂]

theorem isIso_of_mono (h : IsKernelPair f a b) [Mono f] : IsIso a := by
  rw [←
    show _ = a from
      (Category.comp_id _).symm.trans
        ((IsKernelPair.id_of_mono f).isLimit.conePointUniqueUpToIso_inv_comp h.isLimit
          WalkingCospan.left)]
  infer_instance

theorem of_isIso_of_mono [IsIso a] [Mono f] : IsKernelPair f a a := by
  change IsPullback _ _ _ _
  convert (IsPullback.of_horiz_isIso ⟨(rfl : a ≫ 𝟙 X = _ )⟩).paste_vert (IsKernelPair.id_of_mono f)
  all_goals { simp }

end IsKernelPair

end CategoryTheory
