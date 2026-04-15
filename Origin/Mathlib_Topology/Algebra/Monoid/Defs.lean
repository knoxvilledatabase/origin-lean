/-
Extracted from Topology/Algebra/Monoid/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological monoids - definitions

In this file we define three mixin typeclasses:

- `ContinuousMul M` says that the multiplication on `M` is continuous as a function on `M × M`;
- `ContinuousAdd M` says that the addition on `M` is continuous as a function on `M × M`.
- `SeparatelyContinuousMul M` says that the multiplication on `M` is continuous in each argument
  separately. This is strictly weaker than `ContinuousMul M`, but arises frequently in practice in
  functional analysis where one often considers topologies weaker than the norm topology. In these
  topologies it is frequently the case that the multiplication is not jointly continuous, but is
  continuous in each argument separately.

These classes are `Prop`-valued mixins,
i.e., they take data (`TopologicalSpace`, `Mul`/`Add`) as arguments
instead of extending typeclasses with these fields.

We also provide convenience dot notation lemmas like `Filter.Tendsto.mul` and `ContinuousAt.add`.
-/

open scoped Topology

class ContinuousAdd (M : Type*) [TopologicalSpace M] [Add M] : Prop where
  continuous_add : Continuous fun p : M × M => p.1 + p.2
