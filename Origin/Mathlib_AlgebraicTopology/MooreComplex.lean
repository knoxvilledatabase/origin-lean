/-
Extracted from AlgebraicTopology/MooreComplex.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
## Moore complex

We construct the normalized Moore complex, as a functor
`SimplicialObject C ⥤ ChainComplex C ℕ`,
for any abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.

This functor is one direction of the Dold-Kan equivalence, which we're still working towards.

### References

* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex
-/

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits

open Opposite

open scoped Simplicial

namespace AlgebraicTopology

variable {C : Type*} [Category* C] [Abelian C]

attribute [local instance] Abelian.hasPullbacks

/-! The definitions in this namespace are all auxiliary definitions for `NormalizedMooreComplex`
and should usually only be accessed via that. -/

namespace NormalizedMooreComplex

open CategoryTheory.Subobject

variable (X : SimplicialObject C)

def objX : ∀ n : ℕ, Subobject (X.obj (op ⦋n⦌))
  | 0 => ⊤
  | n + 1 => Finset.univ.inf fun k : Fin (n + 1) => kernelSubobject (X.δ k.succ)
