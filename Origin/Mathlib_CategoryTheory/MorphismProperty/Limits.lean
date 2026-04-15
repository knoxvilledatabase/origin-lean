/-
Extracted from CategoryTheory/MorphismProperty/Limits.lean
Genuine: 22 of 32 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Relation of morphism properties with limits

The following predicates are introduces for morphism properties `P`:
* `IsStableUnderBaseChange`: `P` is stable under base change if in all pullback
  squares, the left map satisfies `P` if the right map satisfies it.
* `IsStableUnderCobaseChange`: `P` is stable under cobase change if in all pushout
  squares, the right map satisfies `P` if the left map satisfies it.

We define `P.universally` for the class of morphisms which satisfy `P` after any base change.

We also introduce properties `IsStableUnderProductsOfShape`, `IsStableUnderLimitsOfShape`,
`IsStableUnderFiniteProducts`, and similar properties for colimits and coproducts.

-/

universe w w' v u

namespace CategoryTheory

open Category Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

variable (P : MorphismProperty C)

def pullbacks : MorphismProperty C := fun A B q ↦
  ∃ (X Y : C) (p : X ⟶ Y) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPullback f q p g

lemma pullbacks_mk {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPullback f q p g) (hp : P p) :
    P.pullbacks q :=
  ⟨_, _, _, _, _, hp, sq⟩

lemma le_pullbacks : P ≤ P.pullbacks := by
  intro A B q hq
  exact P.pullbacks_mk IsPullback.of_id_fst hq

lemma pullbacks_monotone : Monotone (pullbacks (C := C)) := by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩

def pushouts : MorphismProperty C := fun X Y q ↦
  ∃ (A B : C) (p : A ⟶ B) (f : A ⟶ X) (g : B ⟶ Y) (_ : P p),
    IsPushout f p q g

lemma pushouts_mk {A B X Y : C} {f : A ⟶ X} {q : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : IsPushout f q p g) (hq : P q) :
    P.pushouts p :=
  ⟨_, _, _, _, _, hq, sq⟩

lemma le_pushouts : P ≤ P.pushouts := by
  intro X Y p hp
  exact P.pushouts_mk IsPushout.of_id_fst hp

lemma pushouts_monotone : Monotone (pushouts (C := C)) := by
  rintro _ _ h _ _ _ ⟨_, _, _, _, _, hp, sq⟩
  exact ⟨_, _, _, _, _, h _ hp, sq⟩

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

class IsStableUnderBaseChange : Prop where
  of_isPullback {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : P g) : P g'

-- INSTANCE (free from Core): :

class IsStableUnderCobaseChange : Prop where
  of_isPushout {A A' B B' : C} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}
    (sq : IsPushout g f f' g') (hf : P f) : P f'

-- INSTANCE (free from Core): :

protected class HasPullbacksAlong {X Y : C} (f : X ⟶ Y) : Prop where
  hasPullback {W} (g : W ⟶ Y) : P g → HasPullback g f

protected class HasPushoutsAlong {X Y : C} (f : X ⟶ Y) : Prop where
  hasPushout {W} (g : X ⟶ W) : P g → HasPushout g f

class IsStableUnderBaseChangeAlong {X Y : C} (f : X ⟶ Y) : Prop where
  of_isPullback {Z W : C} {f' : W ⟶ Z} {g' : W ⟶ X} {g : Z ⟶ Y}
    (pb : IsPullback f' g' g f) : P g → P g'

-- INSTANCE (free from Core): [P.IsStableUnderBaseChange]

class IsStableUnderCobaseChangeAlong {X Y : C} (f : X ⟶ Y) : Prop where
  of_isPushout {Z W : C} {f' : Z ⟶ W} {g' : Y ⟶ W} {g : X ⟶ Z}
    (pb : IsPushout f g g' f') : P g → P g'

-- INSTANCE (free from Core): [P.IsStableUnderCobaseChange]

alias of_isPullback := IsStableUnderBaseChange.of_isPullback

lemma isStableUnderBaseChange_iff_pullbacks_le :
    P.IsStableUnderBaseChange ↔ P.pullbacks ≤ P := by
  constructor
  · intro h _ _ _ ⟨_, _, _, _, _, h₁, h₂⟩
    exact of_isPullback h₂ h₁
  · intro h
    constructor
    intro _ _ _ _ _ _ _ _ h₁ h₂
    exact h _ ⟨_, _, _, _, _, h₂, h₁⟩

lemma pullbacks_le [P.IsStableUnderBaseChange] : P.pullbacks ≤ P := by
  rwa [← isStableUnderBaseChange_iff_pullbacks_le]

variable {P} in

theorem IsStableUnderBaseChange.mk' [RespectsIso P]
    (hP₂ : ∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] (_ : P g),
      P (pullback.fst f g)) :
    IsStableUnderBaseChange P where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    haveI : HasPullback f g := sq.flip.hasPullback
    let e := sq.flip.isoPullback
    rw [← P.cancel_left_of_respectsIso e.inv, sq.flip.isoPullback_inv_fst]
    exact hP₂ _ _ _ f g hg

lemma IsStableUnderBaseChange.of_forall_exists_isPullback {P : MorphismProperty C} [P.RespectsIso]
    (H : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (_ : P g),
      ∃ (T : C) (fst : T ⟶ X) (snd : T ⟶ Y), IsPullback fst snd f g ∧ P fst) :
    P.IsStableUnderBaseChange := by
  refine .mk' fun X Y S f g _ hg ↦ ?_
  obtain ⟨T, fst, snd, h, hfst⟩ := H f g hg
  rwa [← h.isoPullback_inv_fst, P.cancel_left_of_respectsIso]

variable (C)

-- INSTANCE (free from Core): IsStableUnderBaseChange.isomorphisms

-- INSTANCE (free from Core): IsStableUnderBaseChange.monomorphisms

variable {C P}

-- INSTANCE (free from Core): (priority

theorem pullback_fst {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    [P.IsStableUnderBaseChangeAlong f] (H : P g) : P (pullback.fst f g) :=
  IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g).flip H

theorem pullback_snd {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g]
    [P.IsStableUnderBaseChangeAlong g] (H : P f) : P (pullback.snd f g) :=
  IsStableUnderBaseChangeAlong.of_isPullback (IsPullback.of_hasPullback f g) H

set_option backward.isDefEq.respectTransparency false in

theorem baseChange_obj {S S' : C} (f : S' ⟶ S)
    [HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (X : Over S) (H : P X.hom) :
    P ((Over.pullback f).obj X).hom :=
  pullback_snd X.hom f H

set_option backward.isDefEq.respectTransparency false in

theorem pullbackLift_fst_snd [IsStableUnderBaseChange P] {S S' X Y : C} (f : S' ⟶ S)
    {v₁₂ : X ⟶ S} {v₂₂ : Y ⟶ S} {g : X ⟶ Y} (hv₁₂ : v₁₂ = g ≫ v₂₂) [HasPullback v₁₂ f]
    [HasPullback v₂₂ f] (H : P g) : P (pullback.lift (f := v₂₂) (g := f) (pullback.fst v₁₂ f ≫ g)
    (pullback.snd v₁₂ f) (by simp [pullback.condition, ← hv₁₂])) := by
  subst hv₁₂
  refine of_isPullback (f' := pullback.fst (g ≫ v₂₂) f)
    (f := pullback.fst v₂₂ f) ?_ H
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback v₂₂ f)
  simpa using IsPullback.of_hasPullback (g ≫ v₂₂) f
