/-
Extracted from AlgebraicTopology/SimplexCategory/Augmented/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Augmented simplex category

This file defines the `AugmentedSimplexCategory` as the category obtained by adding an initial
object to `SimplexCategory` (using `CategoryTheory.WithInitial`).

This definition provides a canonical full and faithful inclusion functor
`inclusion : SimplexCategory ⥤ AugmentedSimplexCategory`.

We prove that functors out of `AugmentedSimplexCategory` are equivalent to augmented cosimplicial
objects and that functors out of `AugmentedSimplexCategoryᵒᵖ` are equivalent to augmented simplicial
objects, and we provide a translation of the main constructions on augmented (co)simplicial objects
(i.e `drop`, `point` and `toArrow`) in terms of these equivalences.

-/

open CategoryTheory

abbrev AugmentedSimplexCategory := WithInitial SimplexCategory

namespace AugmentedSimplexCategory

variable {C : Type*} [Category* C]
