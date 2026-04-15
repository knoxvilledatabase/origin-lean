/-
Extracted from Probability/Combinatorics/BinomialRandomGraph/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Binomial random graphs

This file constructs the binomial distribution with parameter `p` on simple graphs with
vertices `V`. This is the law `G(V, p)` of binomial random graphs with probability `p`.

## TODO

Add the characteristic predicate for a random graph to follow the binomial random distribution.

## Historical note

This is usually called the Erdős–Rényi model, but this name is historically inaccurate as Erdős and
Rényi introduced a closely related but different model. We therefore choose the name
"binomial random graph" to avoid confusion with this other model and because it is a more
descriptive name.

## Tags

Erdős-Rényi graph, Erdős-Renyi graph, Erdös-Rényi graph, Erdös-Renyi graph, Erdos-Rényi graph,
Erdos-Renyi graph
-/

open MeasureTheory Measure ProbabilityTheory unitInterval

open scoped Finset

namespace SimpleGraph

variable {V : Type*} {p : I}

variable (V p) in

noncomputable def binomialRandom : Measure (SimpleGraph V) :=
  setBer(Sym2.diagSetᶜ, p).comap edgeSet
