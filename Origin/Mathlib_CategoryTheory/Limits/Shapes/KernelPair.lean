/-
Extracted from CategoryTheory/Limits/Shapes/KernelPair.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

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

-- INSTANCE (free from Core): :

theorem id_of_mono [Mono f] : IsKernelPair f (𝟙 _) (𝟙 _) :=
  ⟨⟨rfl⟩, ⟨PullbackCone.isLimitMkIdId _⟩⟩

-- INSTANCE (free from Core): [Mono

variable {f a b}

noncomputable def lift {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    S ⟶ R :=
  PullbackCone.IsLimit.lift k.isLimit _ _ w
