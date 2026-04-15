/-
Extracted from AlgebraicTopology/SimplicialSet/HomotopyCat.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# The homotopy category of a simplicial set

The homotopy category of a simplicial set is defined as a quotient of the free category on its
underlying reflexive quiver (equivalently its one truncation). The quotient imposes an additional
hom relation on this free category, asserting that `f ≫ g = h` whenever `f`, `g`, and `h` are
respectively the 2nd, 0th, and 1st faces of a 2-simplex.

In fact, the associated functor

`SSet.hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ SSet.hoFunctor₂`

is defined by first restricting from simplicial sets to 2-truncated simplicial sets (throwing away
the data that is not used for the construction of the homotopy category) and then composing with an
analogously defined `SSet.hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u}` implemented relative to
the syntax of the 2-truncated simplex category.

In the file `Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.lean` we show the functor
`SSet.hoFunctor` to be left adjoint to the nerve by providing an analogous decomposition of the
nerve functor, made by possible by the fact that nerves of categories are 2-coskeletal, and then
composing a pair of adjunctions, which factor through the category of 2-truncated simplicial sets.
-/

namespace SSet

open CategoryTheory Category Limits Functor Opposite Simplicial Nerve

open SimplexCategory.Truncated SimplicialObject.Truncated

universe v u

def OneTruncation₂ (S : SSet.Truncated 2) := S _⦋0⦌₂
