/-
Extracted from CategoryTheory/Limits/Shapes/BinaryProducts.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Binary (co)products

We define a category `WalkingPair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `HasBinaryProducts` and `HasBinaryCoproducts` assert the existence
of (co)limits shaped as walking pairs.

We include lemmas for simplifying equations involving projections and coprojections, and define
braiding and associating isomorphisms, and the product comparison morphism.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/

universe v v₁ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

inductive WalkingPair : Type
  | left
  | right
  deriving DecidableEq, Inhabited

open WalkingPair

def WalkingPair.swap : WalkingPair ≃ WalkingPair where
  toFun
    | left => right
    | right => left
  invFun
    | left => right
    | right => left
  left_inv j := by cases j <;> rfl
  right_inv j := by cases j <;> rfl
