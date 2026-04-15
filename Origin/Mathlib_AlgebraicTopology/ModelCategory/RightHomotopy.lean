/-
Extracted from AlgebraicTopology/ModelCategory/RightHomotopy.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Right homotopies in model categories

We introduce the types `PrepathObject.RightHomotopy` and `PathObject.RightHomotopy`
of homotopies between morphisms `X ⟶ Y` relative to a (pre)path object of `Y`.
Given two morphisms `f` and `g`, we introduce the relation `RightHomotopyRel f g`
asserting the existence of a path object `P` and
a right homotopy `P.RightHomotopy f g`, and we define the quotient
type `RightHomotopyClass X Y`. We show that if `Y` is a fibrant
object in a model category, then `RightHomotopyRel` is an equivalence
relation on `X ⟶ Y`.

(This file dualizes the definitions in `Mathlib/AlgebraicTopology/ModelCategory/LeftHomotopy.lean`.)

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

namespace PrepathObject

variable {Y : C} (P : PrepathObject Y) {X : C}

structure RightHomotopy (f g : X ⟶ Y) where
  /-- a morphism from the source to the pre-path object -/
  h : X ⟶ P.P
  h₀ : h ≫ P.p₀ = f := by cat_disch
  h₁ : h ≫ P.p₁ = g := by cat_disch

namespace RightHomotopy

attribute [reassoc (attr := simp)] h₀ h₁
