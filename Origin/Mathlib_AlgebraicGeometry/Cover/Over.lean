/-
Extracted from AlgebraicGeometry/Cover/Over.lean
Genuine: 7 of 18 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!

# Covers of schemes over a base

In this file we define the typeclass `Cover.Over`. For a cover `𝒰` of an `S`-scheme `X`,
the datum `𝒰.Over S` contains `S`-scheme structures on the components of `𝒰` and asserts
that the component maps are morphisms of `S`-schemes.

We provide instances of `𝒰.Over S` for standard constructions on covers.

-/

universe v u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} (S : Scheme.{u})

abbrev asOverProp (X : Scheme.{u}) (S : Scheme.{u}) [X.Over S] (h : P (X ↘ S)) : P.Over ⊤ S :=
  ⟨X.asOver S, h⟩

abbrev Hom.asOverProp {X Y : Scheme.{u}} (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S]
    [f.IsOver S] {hX : P (X ↘ S)} {hY : P (Y ↘ S)} : X.asOverProp S hX ⟶ Y.asOverProp S hY :=
  ⟨f.asOver S, trivial, trivial⟩

protected class Cover.Over {P : MorphismProperty Scheme.{u}} {X : Scheme.{u}} [X.Over S]
    (𝒰 : X.Cover P) where
  over (j : 𝒰.J) : (𝒰.obj j).Over S := by infer_instance
  isOver_map (j : 𝒰.J) : (𝒰.map j).IsOver S := by infer_instance

attribute [instance] Cover.Over.over Cover.Over.isOver_map

instance [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y) [X.Over S] [Y.Over S]
    [f.IsOver S] [IsIso f] : (coverOfIsIso (P := P) f).Over S where
  over _ := inferInstanceAs <| X.Over S
  isOver_map _ := inferInstanceAs <| f.IsOver S

section

variable [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]

variable {X W : Scheme.{u}} (𝒰 : X.Cover P) (f : W ⟶ X) [W.Over S] [X.Over S]
  [𝒰.Over S] [f.IsOver S]

@[simps]
def Cover.pullbackCoverOver : W.Cover P where
  J := 𝒰.J
  obj x := (pullback (f.asOver S) ((𝒰.map x).asOver S)).left
  map x := (pullback.fst (f.asOver S) ((𝒰.map x).asOver S)).left
  f x := 𝒰.f (f.base x)
  covers x := (mem_range_iff_of_surjective ((𝒰.pullbackCover f).map (𝒰.f (f.base x))) _
    ((PreservesPullback.iso (Over.forget S) (f.asOver S) ((𝒰.map _).asOver S)).inv)
    (PreservesPullback.iso_inv_fst _ _ _) x).mp ((𝒰.pullbackCover f).covers x)
  map_prop j := by
    dsimp only
    rw [← Over.forget_map, ← PreservesPullback.iso_hom_fst, P.cancel_left_of_respectsIso]
    exact P.pullback_fst _ _ (𝒰.map_prop j)

instance (j : 𝒰.J) : ((𝒰.pullbackCoverOver S f).obj j).Over S where
  hom := (pullback (f.asOver S) ((𝒰.map j).asOver S)).hom

instance : (𝒰.pullbackCoverOver S f).Over S where
  isOver_map j := { comp_over := by exact Over.w (pullback.fst (f.asOver S) ((𝒰.map j).asOver S)) }

@[simps]
def Cover.pullbackCoverOver' : W.Cover P where
  J := 𝒰.J
  obj x := (pullback ((𝒰.map x).asOver S) (f.asOver S)).left
  map x := (pullback.snd ((𝒰.map x).asOver S) (f.asOver S)).left
  f x := 𝒰.f (f.base x)
  covers x := (mem_range_iff_of_surjective ((𝒰.pullbackCover' f).map (𝒰.f (f.base x))) _
    ((PreservesPullback.iso (Over.forget S) ((𝒰.map _).asOver S) (f.asOver S)).inv)
    (PreservesPullback.iso_inv_snd _ _ _) x).mp ((𝒰.pullbackCover' f).covers x)
  map_prop j := by
    dsimp only
    rw [← Over.forget_map, ← PreservesPullback.iso_hom_snd, P.cancel_left_of_respectsIso]
    exact P.pullback_snd _ _ (𝒰.map_prop j)

instance (j : 𝒰.J) : ((𝒰.pullbackCoverOver' S f).obj j).Over S where
  hom := (pullback ((𝒰.map j).asOver S) (f.asOver S)).hom

instance : (𝒰.pullbackCoverOver' S f).Over S where
  isOver_map j := { comp_over := by exact Over.w (pullback.snd ((𝒰.map j).asOver S) (f.asOver S)) }

variable {Q : MorphismProperty Scheme.{u}} [Q.HasOfPostcompProperty Q]
  [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]

variable (hX : Q (X ↘ S)) (hW : Q (W ↘ S)) (hQ : ∀ j, Q (𝒰.obj j ↘ S))

@[simps (config := .lemmasOnly)]
def Cover.pullbackCoverOverProp : W.Cover P where
  J := 𝒰.J
  obj x := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.map x).asOverProp (hX := hQ x) (hY := hX) S)).left
  map x := (pullback.fst (f.asOverProp S) ((𝒰.map x).asOverProp S)).left
  f x := 𝒰.f (f.base x)
  covers x := (mem_range_iff_of_surjective ((𝒰.pullbackCover f).map (𝒰.f (f.base x))) _
    ((PreservesPullback.iso (MorphismProperty.Over.forget Q _ _ ⋙ Over.forget S)
      (f.asOverProp S) ((𝒰.map _).asOverProp S)).inv)
    (PreservesPullback.iso_inv_fst _ _ _) x).mp ((𝒰.pullbackCover f).covers x)
  map_prop j := by
    dsimp only
    rw [← Over.forget_map, MorphismProperty.Comma.toCommaMorphism_eq_hom,
      ← MorphismProperty.Comma.forget_map, ← Functor.comp_map]
    rw [← PreservesPullback.iso_hom_fst, P.cancel_left_of_respectsIso]
    exact P.pullback_fst _ _ (𝒰.map_prop j)

instance (j : 𝒰.J) : ((𝒰.pullbackCoverOverProp S f hX hW hQ).obj j).Over S where
  hom := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.map j).asOverProp (hX := hQ j) (hY := hX) S)).hom

instance : (𝒰.pullbackCoverOverProp S f hX hW hQ).Over S where
  isOver_map j :=
    { comp_over := by exact (pullback.fst (f.asOverProp S) ((𝒰.map j).asOverProp S)).w }

@[simps (config := .lemmasOnly)]
def Cover.pullbackCoverOverProp' : W.Cover P where
  J := 𝒰.J
  obj x := (pullback ((𝒰.map x).asOverProp (hX := hQ x) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).left
  map x := (pullback.snd ((𝒰.map x).asOverProp S) (f.asOverProp S)).left
  f x := 𝒰.f (f.base x)
  covers x := (mem_range_iff_of_surjective ((𝒰.pullbackCover' f).map (𝒰.f (f.base x))) _
    ((PreservesPullback.iso (MorphismProperty.Over.forget Q _ _ ⋙ Over.forget S)
      ((𝒰.map _).asOverProp S) (f.asOverProp S)).inv)
    (PreservesPullback.iso_inv_snd _ _ _) x).mp ((𝒰.pullbackCover' f).covers x)
  map_prop j := by
    dsimp only
    rw [← Over.forget_map, MorphismProperty.Comma.toCommaMorphism_eq_hom,
      ← MorphismProperty.Comma.forget_map, ← Functor.comp_map]
    rw [← PreservesPullback.iso_hom_snd, P.cancel_left_of_respectsIso]
    exact P.pullback_snd _ _ (𝒰.map_prop j)

instance (j : 𝒰.J) : ((𝒰.pullbackCoverOverProp' S f hX hW hQ).obj j).Over S where
  hom := (pullback ((𝒰.map j).asOverProp (hX := hQ j) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).hom

instance : (𝒰.pullbackCoverOverProp' S f hX hW hQ).Over S where
  isOver_map j :=
    { comp_over := by exact (pullback.snd ((𝒰.map j).asOverProp S) (f.asOverProp S)).w }

end

variable [P.IsStableUnderComposition]

variable {X : Scheme.{u}} (𝒰 : X.Cover P) (𝒱 : ∀ x, (𝒰.obj x).Cover P)
  [X.Over S] [𝒰.Over S] [∀ x, (𝒱 x).Over S]

instance (j : (𝒰.bind 𝒱).J) : ((𝒰.bind 𝒱).obj j).Over S :=
  inferInstanceAs <| ((𝒱 j.1).obj j.2).Over S

instance {X : Scheme.{u}} (𝒰 : X.Cover P) (𝒱 : ∀ x, (𝒰.obj x).Cover P)
    [X.Over S] [𝒰.Over S] [∀ x, (𝒱 x).Over S] : (𝒰.bind 𝒱).Over S where
  over := fun ⟨i, j⟩ ↦ inferInstanceAs <| ((𝒱 i).obj j).Over S
  isOver_map := fun ⟨i, j⟩ ↦ { comp_over := by simp }

end AlgebraicGeometry.Scheme
