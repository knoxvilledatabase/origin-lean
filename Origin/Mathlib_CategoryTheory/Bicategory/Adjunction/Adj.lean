/-
Extracted from CategoryTheory/Bicategory/Adjunction/Adj.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The bicategory of adjunctions in a bicategory

Given a bicategory `B`, we construct a bicategory `Adj B` that has essentially
the same objects as `B` but whose `1`-morphisms are adjunctions (in the same
direction as the left adjoints), and `2`-morphisms are tuples of mate maps
between the left and right adjoints (where the map between right
adjoints is in the opposite direction).

Certain pseudofunctors to the bicategory `Adj Cat` are analogous to bifibered categories:
in various contexts, this may be used in order to formalize the properties of
both pullback and pushforward functors.

## References

* https://ncatlab.org/nlab/show/2-category+of+adjunctions
* https://ncatlab.org/nlab/show/transformation+of+adjoints
* https://ncatlab.org/nlab/show/mate

-/

universe w v u

namespace CategoryTheory

namespace Bicategory

structure Adj (B : Type u) [Bicategory.{w, v} B] where
  /-- If `a : Adj B`, `a.obj : B` is the underlying object of the bicategory `B`. -/
  obj : B

variable {B : Type u} [Bicategory.{w, v} B]

namespace Adj
