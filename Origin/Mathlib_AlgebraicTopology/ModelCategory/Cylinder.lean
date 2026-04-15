/-
Extracted from AlgebraicTopology/ModelCategory/Cylinder.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cylinders

We introduce a notion of cylinder for an object `A : C` in a model category.
It consists of an object `I`, a weak equivalence `π : I ⟶ A` equipped with two sections
`i₀` and `i₁`. This notion shall be important in the definition of "left homotopies"
in model categories.

## Implementation notes

The most important definition in this file is `Cylinder A`. This structure
extends another structure `Precylinder A` (which does not assume that `C`
has a notion of weak equivalences, which can be interesting in situations
where we have not yet obtained the model category axioms).

The good properties of cylinders are stated as typeclasses `Cylinder.IsGood`
and `Cylinder.IsVeryGood`.

The existence of very good cylinder objects in model categories is stated
in the lemma `Cylinder.exists_very_good`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* https://ncatlab.org/nlab/show/cylinder+object

-/

universe v u

open CategoryTheory Category Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

structure Precylinder (A : C) where
  /-- the underlying object of a (pre)cylinder -/
  I : C
  /-- the first "inclusion" in the (pre)cylinder -/
  i₀ : A ⟶ I
  /-- the second "inclusion" in the (pre)cylinder -/
  i₁ : A ⟶ I
  /-- the codiagonal of the (pre)cylinder -/
  π : I ⟶ A
  i₀_π : i₀ ≫ π = 𝟙 A := by cat_disch
  i₁_π : i₁ ≫ π = 𝟙 A := by cat_disch

namespace Precylinder

attribute [reassoc (attr := simp)] i₀_π i₁_π

variable {A : C} (P : Precylinder A)
