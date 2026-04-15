/-
Extracted from Analysis/Convex/Side.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sides of affine subspaces

This file defines notions of two points being on the same or opposite sides of an affine subspace.

## Main definitions

* `s.WSameSide x y`: The points `x` and `y` are weakly on the same side of the affine
  subspace `s`.
* `s.SSameSide x y`: The points `x` and `y` are strictly on the same side of the affine
  subspace `s`.
* `s.WOppSide x y`: The points `x` and `y` are weakly on opposite sides of the affine
  subspace `s`.
* `s.SOppSide x y`: The points `x` and `y` are strictly on opposite sides of the affine
  subspace `s`.

-/

variable {R V V' P P' : Type*}

open AffineEquiv AffineMap

namespace AffineSubspace

section StrictOrderedCommRing

variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

def WSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  ∃ᵉ (p₁ ∈ s) (p₂ ∈ s), SameRay R (x -ᵥ p₁) (y -ᵥ p₂)

def SSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WSameSide x y ∧ x ∉ s ∧ y ∉ s

def WOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  ∃ᵉ (p₁ ∈ s) (p₂ ∈ s), SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)

def SOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WOppSide x y ∧ x ∉ s ∧ y ∉ s

theorem WSameSide.map {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) (f : P →ᵃ[R] P') :
    (s.map f).WSameSide (f x) (f y) := by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, ?_⟩
  simp_rw [← linearMap_vsub]
  exact h.map f.linear

theorem _root_.Function.Injective.wSameSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).WSameSide (f x) (f y) ↔ s.WSameSide x y := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exact h

theorem _root_.Function.Injective.sSameSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).SSameSide (f x) (f y) ↔ s.SSameSide x y := by
  simp_rw [SSameSide, hf.wSameSide_map_iff, mem_map_iff_mem_of_injective hf]
