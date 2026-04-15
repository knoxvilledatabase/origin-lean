/-
Extracted from Analysis/Normed/Lp/ProdLp.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `L^p` distance on products of two metric spaces
Given two metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a parameter `p : ℝ≥0∞`, that also induce
the product topology. We define them in this file. For `0 < p < ∞`, the distance on `α × β`
is given by
$$
d(x, y) = \left(d(x_1, y_1)^p + d(x_2, y_2)^p\right)^{1/p}.
$$
For `p = ∞` the distance is the supremum of the distances and `p = 0` the distance is the
cardinality of the elements that are not equal.

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Prod-type, named
`WithLp p (α × β)`. The assumption `[Fact (1 ≤ p)]` is required for the metric and normed space
instances.

We ensure that the topology, bornology and uniform structure on `WithLp p (α × β)` are (defeq to)
the product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

If you wish to endow a type synonym of `α × β` with the `L^p` distance, you can use
`pseudoMetricSpaceToProd` and the declarations below that one.


## Implementation notes

This file is a straight-forward adaptation of `Mathlib/Analysis/Normed/Lp/PiLp.lean`.

## TODO

TODO: the results about uniformity and bornology in the `Aux` section should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.

-/

open Real Set Filter RCLike Bornology Uniformity Topology NNReal ENNReal

noncomputable section

variable (p : ℝ≥0∞) (𝕜 α β : Type*)

namespace WithLp

section algebra

variable {p 𝕜 α β}

variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]

variable (x y : WithLp p (α × β)) (c : 𝕜)

protected def fst (x : WithLp p (α × β)) : α := (ofLp x).fst

protected def snd (x : WithLp p (α × β)) : β := (ofLp x).snd
