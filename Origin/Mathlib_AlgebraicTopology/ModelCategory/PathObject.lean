/-
Extracted from AlgebraicTopology/ModelCategory/PathObject.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Path objects

We introduce a notion of path object for an object `A : C` in a model category.
It consists of an object `P`, a weak equivalence `ι : A ⟶ P` equipped with two retractions
`p₀` and `p₁`. This notion shall be important in the definition of "right homotopies"
in model categories.

This file dualizes the definitions in the file
`Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean`.

## Implementation notes

The most important definition in this file is `PathObject A`. This structure
extends another structure `PrepathObject A` (which does not assume that `C`
has a notion of weak equivalences, which can be interesting in situations
where we have not yet obtained the model category axioms).

The good properties of path objects are stated as typeclasses `PathObject.IsGood`
and `PathObject.IsVeryGood`.

The existence of very good path objects in model categories is stated
in the lemma `PathObject.exists_very_good`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* https://ncatlab.org/nlab/show/path+space+object

-/

universe v u

open CategoryTheory Category Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

structure PrepathObject (A : C) where
  /-- the underlying object of a (pre)path object -/
  P : C
  /-- the first "projection" from the (pre)path object -/
  p₀ : P ⟶ A
  /-- the second "projection" from the (pre)path object -/
  p₁ : P ⟶ A
  /-- the diagonal of the (pre)path object -/
  ι : A ⟶ P
  ι_p₀ : ι ≫ p₀ = 𝟙 A := by aesop_cat
  ι_p₁ : ι ≫ p₁ = 𝟙 A := by aesop_cat

namespace PrepathObject

attribute [reassoc (attr := simp)] ι_p₀ ι_p₁

variable {A : C} (P : PrepathObject A)
