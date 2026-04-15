/-
Extracted from Topology/Order/OrderClosed.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Order-closed topologies

In this file we introduce 3 typeclass mixins that relate topology and order structures:

- `ClosedIicTopology` says that all the intervals $(-∞, a]$ (formally, `Set.Iic a`)
  are closed sets;
- `ClosedIciTopology` says that all the intervals $[a, +∞)$ (formally, `Set.Ici a`)
  are closed sets;
- `OrderClosedTopology` says that the set of points `(x, y)` such that `x ≤ y`
  is closed in the product topology.

The last predicate implies the first two.

We prove many basic properties of such topologies.

## Main statements

This file contains the proofs of the following facts.
For exact requirements
(`OrderClosedTopology` vs `ClosedIciTopology` vs `ClosedIicTopology`,
`Preorder` vs `PartialOrder` vs `LinearOrder`, etc.)
see their statements.

### Open / closed sets

* `isOpen_lt` : if `f` and `g` are continuous functions, then `{x | f x < g x}` is open;
* `isOpen_Iio`, `isOpen_Ioi`, `isOpen_Ioo` : open intervals are open;
* `isClosed_le` : if `f` and `g` are continuous functions, then `{x | f x ≤ g x}` is closed;
* `isClosed_Iic`, `isClosed_Ici`, `isClosed_Icc` : closed intervals are closed;
* `frontier_le_subset_eq`, `frontier_lt_subset_eq` : frontiers of both `{x | f x ≤ g x}`
  and `{x | f x < g x}` are included by `{x | f x = g x}`;

### Convergence and inequalities

* `le_of_tendsto_of_tendsto` : if `f` converges to `a`, `g` converges to `b`, and eventually
  `f x ≤ g x`, then `a ≤ b`
* `le_of_tendsto`, `ge_of_tendsto` : if `f` converges to `a` and eventually `f x ≤ b`
  (resp., `b ≤ f x`), then `a ≤ b` (resp., `b ≤ a`); we also provide primed versions
  that assume the inequalities to hold for all `x`.

### Min, max, `sSup` and `sInf`

* `Continuous.min`, `Continuous.max`: pointwise `min`/`max` of two continuous functions is
  continuous.
* `Tendsto.min`, `Tendsto.max` : if `f` tends to `a` and `g` tends to `b`, then their pointwise
  `min`/`max` tend to `min a b` and `max a b`, respectively.
-/

open Set Filter TopologicalSpace

open OrderDual (toDual)

open scoped Topology

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

class ClosedIicTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `(-∞, a]` is closed. -/
  isClosed_Iic (a : α) : IsClosed (Iic a)
