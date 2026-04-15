/-
Extracted from AlgebraicTopology/SimplicialSet/NonDegenerateSimplices.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The partially ordered type of non degenerate simplices of a simplicial set

In this file, we introduce the partially ordered type `X.N` of
non degenerate simplices of a simplicial set `X`. We obtain
an embedding `X.orderEmbeddingN : X.N ↪o X.Subcomplex` which sends
a non degenerate simplex to the subcomplex of `X` it generates.

Given an arbitrary simplex `x : X.S`, we show that there is a unique
non degenerate `x.toN : X.N` such that `x.toN.subcomplex = x.subcomplex`.

-/

universe u

open CategoryTheory Simplicial

namespace SSet

variable (X : SSet.{u})

structure N extends X.S where mk' ::
  nonDegenerate : simplex ∈ X.nonDegenerate _

namespace N

variable {X}

lemma mk'_surjective (s : X.N) :
    ∃ (t : X.S) (ht : t.simplex ∈ X.nonDegenerate _), s = mk' t ht :=
  ⟨s.toS, s.nonDegenerate, rfl⟩
