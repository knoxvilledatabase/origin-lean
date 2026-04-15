/-
Extracted from CategoryTheory/DifferentialObject.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Differential objects in a category.

A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : obj ⟶ obj⟦1⟧`, such that `d^2 = 0`.

We build the category of differential objects, and some basic constructions
such as the forgetful functor, zero morphisms and zero objects, and the shift functor
on differential objects.
-/

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (S : Type*) [AddMonoidWithOne S] (C : Type u) [Category.{v} C]

variable [HasZeroMorphisms C] [HasShift C S]

structure DifferentialObject where
  /-- The underlying object of a differential object. -/
  obj : C
  /-- The differential of a differential object. -/
  d : obj ⟶ obj⟦(1 : S)⟧
  /-- The differential `d` satisfies that `d² = 0`. -/
  d_squared : d ≫ d⟦(1 : S)⟧' = 0 := by cat_disch

attribute [reassoc (attr := simp)] DifferentialObject.d_squared

variable {S C}

namespace DifferentialObject
