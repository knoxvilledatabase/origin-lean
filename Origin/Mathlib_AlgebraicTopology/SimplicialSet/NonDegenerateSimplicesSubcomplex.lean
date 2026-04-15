/-
Extracted from AlgebraicTopology/SimplicialSet/NonDegenerateSimplicesSubcomplex.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The type of nondegenerate simplices not in a subcomplex

In this file, given a subcomplex `A` of a simplicial set `X`,
we introduce the type `A.N` of nondegenerate simplices of `X`
that are not in `A`.

-/

universe u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

structure N extends X.N where mk' ::
  notMem : simplex ∉ A.obj _

namespace N

variable {A}

lemma mk'_surjective (s : A.N) :
    ∃ (t : X.N) (ht : t.simplex ∉ A.obj _), s = mk' t ht :=
  ⟨s.toN, s.notMem, rfl⟩
