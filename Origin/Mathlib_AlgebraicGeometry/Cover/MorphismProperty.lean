/-
Extracted from AlgebraicGeometry/Cover/MorphismProperty.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Covers of schemes

This file provides the basic API for covers of schemes. A cover of a scheme `X` with respect to
a morphism property `P` is a jointly surjective indexed family of scheme morphisms with
target `X` all satisfying `P`.

## Implementation details

The definition on the pullback of a cover along a morphism depends on results that
are developed later in the import tree. Hence in this file, they have additional assumptions
that will be automatically satisfied in later files. The motivation here is that we already
know that these assumptions are satisfied for open immersions and hence the cover API for open
immersions can be used to deduce these assumptions in the general case.

-/

noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

variable (K : Precoverage Scheme.{u})

class JointlySurjective (K : Precoverage Scheme.{u}) : Prop where
  exists_eq {X : Scheme.{u}} (S : Presieve X) (hS : S ∈ K X) (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ x ∈ Set.range g

abbrev Cover (K : Precoverage Scheme.{u}) := Precoverage.ZeroHypercover.{v} K

variable {K}

variable {X Y Z : Scheme.{u}} (𝒰 : X.Cover K) (f : X ⟶ Z) (g : Y ⟶ Z)

variable [∀ x, HasPullback (𝒰.f x ≫ f) g]

lemma Cover.exists_eq [JointlySurjective K] (𝒰 : X.Cover K) (x : X) :
    ∃ i y, 𝒰.f i y = x := by
  obtain ⟨Y, g, ⟨i⟩, y, hy⟩ := JointlySurjective.exists_eq 𝒰.presieve₀ 𝒰.mem₀ x
  use i, y

def Cover.idx [JointlySurjective K] (𝒰 : X.Cover K) (x : X) : 𝒰.I₀ :=
  (𝒰.exists_eq x).choose

lemma Cover.covers [JointlySurjective K] (𝒰 : X.Cover K) (x : X) :
    x ∈ Set.range (𝒰.f (𝒰.idx x)) :=
  (𝒰.exists_eq x).choose_spec

theorem Cover.iUnion_range [JointlySurjective K] {X : Scheme.{u}} (𝒰 : X.Cover K) :
    ⋃ i, Set.range (𝒰.f i) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact 𝒰.exists_eq x

-- INSTANCE (free from Core): Cover.nonempty_of_nonempty

section MorphismProperty

variable {P Q : MorphismProperty Scheme.{u}}
