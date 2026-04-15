/-
Extracted from CategoryTheory/EqToHom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Morphisms from equations between objects.

When working categorically, sometimes one encounters an equation `h : X = Y` between objects.

Your initial aversion to this is natural and appropriate:
you're in for some trouble, and if there is another way to approach the problem that won't
rely on this equality, it may be worth pursuing.

You have two options:
1. Use the equality `h` as one normally would in Lean (e.g. using `rw` and `subst`).
   This may immediately cause difficulties, because in category theory everything is dependently
   typed, and equations between objects quickly lead to nasty goals with `eq.rec`.
2. Promote `h` to a morphism using `eqToHom h : X ⟶ Y`, or `eqToIso h : X ≅ Y`.

This file introduces various `simp` lemmas which in favourable circumstances
result in the various `eqToHom` morphisms to drop out at the appropriate moment!
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite

def eqToHom {C : Type u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y) :
    X ⟶ Y := by
  rw [p]
  exact 𝟙 _
