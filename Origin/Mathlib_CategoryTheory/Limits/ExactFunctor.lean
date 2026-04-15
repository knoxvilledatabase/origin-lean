/-
Extracted from CategoryTheory/Limits/ExactFunctor.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bundled exact functors

We say that a functor `F` is left exact if it preserves finite limits, it is right exact if it
preserves finite colimits, and it is exact if it is both left exact and right exact.

In this file, we define the categories of bundled left exact, right exact and exact functors.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable (C) (D)

def leftExactFunctor : ObjectProperty (C ⥤ D) :=
  fun F ↦ PreservesFiniteLimits F

variable {C D} in
