/-
Extracted from AlgebraicTopology/ModelCategory/LeftHomotopy.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Left homotopies in model categories

We introduce the types `Precylinder.LeftHomotopy` and `Cylinder.LeftHomotopy`
of homotopies between morphisms `X ⟶ Y` relative to a (pre)cylinder of `X`.
Given two morphisms `f` and `g`, we introduce the relation `LeftHomotopyRel f g`
asserting the existence of a cylinder object `P` and
a left homotopy `P.LeftHomotopy f g`, and we define the quotient
type `LeftHomotopyClass X Y`. We show that if `X` is a cofibrant
object in a model category, then `LeftHomotopyRel` is an equivalence
relation on `X ⟶ Y`.

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

namespace Precylinder

variable {X : C} (P : Precylinder X) {Y : C}

structure LeftHomotopy (f g : X ⟶ Y) where
  /-- a morphism from the (pre)cylinder object to the target -/
  h : P.I ⟶ Y
  h₀ : P.i₀ ≫ h = f := by cat_disch
  h₁ : P.i₁ ≫ h = g := by cat_disch

namespace LeftHomotopy

attribute [reassoc (attr := simp)] h₀ h₁
