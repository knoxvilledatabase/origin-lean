/-
Extracted from CategoryTheory/MorphismProperty/Local.lean
Genuine: 13 of 17 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Locality conditions on morphism properties

In this file we define locality conditions on morphism properties in a category. Let `K` be a
precoverage in a category `C` and `P` be a morphism property on `C` that respects isomorphisms.

We say that

- `P` is local at the target if for every `f : X ⟶ Y`, `P` holds for `f` if and only if it holds
  for the restrictions of `f` to `Uᵢ` for a
  `K`-cover `{Uᵢ}` of `Y`.
- `P` is local at the source if for every `f : X ⟶ Y`, `P` holds for `f` if and only if it holds
  for the restrictions of `f` to `Uᵢ` for a `K`-cover `{Uᵢ}` of `X`.

## Implementation details

The covers appearing in the definitions have index type in the morphism universe of `C`.

## TODOs

- Define source and target local closure of a morphism property.
-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (K : Precoverage C)

class IsLocalAtTarget (P : MorphismProperty C) (K : Precoverage C) [K.HasPullbacks]
    extends RespectsIso P where
  /-- If `P` holds for `f : X ⟶ Y`, it also holds for `f` restricted to `Uᵢ` for any
  `K`-cover `𝒰` of `Y`. -/
  pullbackSnd {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K Y)
    (i : 𝒰.I₀) (hf : P f) : P (pullback.snd f (𝒰.f i))
  /-- If `P` holds for `f` restricted to `Uᵢ` for all `i`, it also holds for `f : X ⟶ Y` for any
  `K`-cover `𝒰` of `Y`. -/
  of_zeroHypercover {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K Y)
    (h : ∀ i, P (pullback.snd f (𝒰.f i))) : P f

namespace IsLocalAtTarget

variable {P : MorphismProperty C} {K L : Precoverage C} [K.HasPullbacks]

lemma mk_of_iff [P.RespectsIso]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{v} K Y),
      P f ↔ ∀ i, P (pullback.snd f (𝒰.f i))) :
    P.IsLocalAtTarget K where
  pullbackSnd 𝒰 i h := (H _ 𝒰).mp h i
  of_zeroHypercover 𝒰 h := (H _ 𝒰).mpr h

lemma mk_of_isStableUnderBaseChange [P.IsStableUnderBaseChange]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{v} K Y),
      (∀ i, P (pullback.snd f (𝒰.f i))) → P f) :
    P.IsLocalAtTarget K where
  pullbackSnd _ _ hf := P.pullback_snd _ _ hf
  of_zeroHypercover _ := H _ _

lemma of_le [L.HasPullbacks] [IsLocalAtTarget P L] (hle : K ≤ L) : IsLocalAtTarget P K where
  pullbackSnd 𝒰 i hf := pullbackSnd (𝒰.weaken hle) i hf
  of_zeroHypercover 𝒰 := of_zeroHypercover (𝒰.weaken hle)

-- INSTANCE (free from Core): top

variable [IsLocalAtTarget P K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K Y)

lemma of_isPullback {X' : C} (i : 𝒰.I₀) {fst : X' ⟶ X} {snd : X' ⟶ 𝒰.X i}
    (h : IsPullback fst snd f (𝒰.f i)) (hf : P f) :
    P snd := by
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_snd]
  exact pullbackSnd _ _ hf

lemma iff_of_zeroHypercover : P f ↔ ∀ i, P (pullback.snd f (𝒰.f i)) :=
  ⟨fun hf _ ↦ pullbackSnd _ _ hf, fun h ↦ of_zeroHypercover _ h⟩

-- INSTANCE (free from Core): inf

end IsLocalAtTarget

lemma of_zeroHypercover_target {P : MorphismProperty C} {K : Precoverage C} [K.HasPullbacks]
    [P.IsLocalAtTarget K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y)
    [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : ∀ i, P (pullback.snd f (𝒰.f i))) :
    P f := by
  rw [IsLocalAtTarget.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_target := IsLocalAtTarget.iff_of_zeroHypercover

class IsLocalAtSource (P : MorphismProperty C) (K : Precoverage C) extends RespectsIso P where
  /-- If `P` holds for `f : X ⟶ Y`, it also holds for `𝒰.f i ≫ f` for any `K`-cover `𝒰` of `X`. -/
  comp {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K X) (i : 𝒰.I₀)
    (hf : P f) : P (𝒰.f i ≫ f)
  /-- If `P` holds for `𝒰.f i ≫ f` for all `i`, it holds for `f : X ⟶ Y` for any `K`-cover
  `𝒰` of X. -/
  of_zeroHypercover {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K X) :
    (∀ i, P (𝒰.f i ≫ f)) → P f

namespace IsLocalAtSource

variable {P : MorphismProperty C} {K L : Precoverage C}

lemma mk_of_iff [P.RespectsIso]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{v} K X),
      P f ↔ ∀ i, P (𝒰.f i ≫ f)) :
    P.IsLocalAtSource K where
  comp 𝒰 i h := (H _ 𝒰).mp h i
  of_zeroHypercover 𝒰 h := (H _ 𝒰).mpr h

lemma of_le [IsLocalAtSource P L] (hle : K ≤ L) : IsLocalAtSource P K where
  comp 𝒰 i hf := comp (𝒰.weaken hle) i hf
  of_zeroHypercover 𝒰 h := of_zeroHypercover (𝒰.weaken hle) h

-- INSTANCE (free from Core): top

variable [IsLocalAtSource P K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{v} K X)

lemma iff_of_zeroHypercover : P f ↔ ∀ i, P (𝒰.f i ≫ f) :=
  ⟨fun hf i ↦ comp _ i hf, fun h ↦ of_zeroHypercover _ h⟩

-- INSTANCE (free from Core): inf

end IsLocalAtSource

lemma of_zeroHypercover_source {P : MorphismProperty C} {K : Precoverage C}
    [P.IsLocalAtSource K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X)
    [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : ∀ i, P (𝒰.f i ≫ f)) :
    P f := by
  rw [IsLocalAtSource.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_source := IsLocalAtSource.iff_of_zeroHypercover

end MorphismProperty

lemma eq_of_zeroHypercover_target [HasEqualizers C] [HasPullbacks C] {X Y S : C} {f g : X ⟶ Y}
    {s : X ⟶ S} {t : Y ⟶ S} (hf : f ≫ t = s) (hg : g ≫ t = s) {J : Precoverage C}
    (𝒰 : Precoverage.ZeroHypercover.{v} J S) [J.IsStableUnderBaseChange]
    [(MorphismProperty.isomorphisms C).IsLocalAtTarget J]
    (H : ∀ i,
      pullback.map s (𝒰.f i) t (𝒰.f i) f (𝟙 (𝒰.X i)) (𝟙 S) (by simp [hf]) (by simp) =
        pullback.map s (𝒰.f i) t (𝒰.f i) g (𝟙 (𝒰.X i)) (𝟙 S) (by simp [hg]) (by simp)) :
    f = g := by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  rw [(MorphismProperty.isomorphisms C).iff_of_zeroHypercover_target (𝒰.pullback₁ s)]
  intro i
  have : pullback.snd (equalizer.ι f g) (pullback.fst s (𝒰.f i)) =
      (equalizerPullbackMapIso hf hg _).inv ≫ equalizer.ι _ _ := by
    ext <;> simp [pullback.condition]
  simpa [this] using equalizer.ι_of_eq (H i)

end CategoryTheory
