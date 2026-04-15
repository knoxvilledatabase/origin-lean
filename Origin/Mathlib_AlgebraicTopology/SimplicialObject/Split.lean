/-
Extracted from AlgebraicTopology/SimplicialObject/Split.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Split simplicial objects

In this file, we introduce the notion of split simplicial object.
If `C` is a category that has finite coproducts, a splitting
`s : Splitting X` of a simplicial object `X` in `C` consists
of the datum of a sequence of objects `s.N : ℕ → C` (which
we shall refer to as "nondegenerate simplices") and a
sequence of morphisms `s.ι n : s.N n → X _⦋n⦌` that have
the property that a certain canonical map identifies `X _⦋n⦌`
with the coproduct of objects `s.N i` indexed by all possible
epimorphisms `⦋n⦌ ⟶ ⦋i⦌` in `SimplexCategory`. (We do not
assume that the morphisms `s.ι n` are monomorphisms: in the
most common categories, this would be a consequence of the
axioms.)

Simplicial objects equipped with a splitting form a category
`SimplicialObject.Split C`.

## References
* [Stacks: Splitting simplicial objects] https://stacks.math.columbia.edu/tag/017O

-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite SimplexCategory

open Simplicial

universe u

variable {C : Type*} [Category* C]

namespace SimplicialObject

namespace Splitting

def IndexSet (Δ : SimplexCategoryᵒᵖ) :=
  Σ Δ' : SimplexCategoryᵒᵖ, { α : Δ.unop ⟶ Δ'.unop // Epi α }

namespace IndexSet
