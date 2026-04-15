/-
Extracted from Topology/OpenPartialHomeomorph/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Partial homeomorphisms: definitions

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`OpenPartialHomeomorph X Y` is an extension of `PartialEquiv X Y`, i.e., it is a pair of functions
`e.toFun` and `e.invFun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.toFun x` and `e.invFun x`.

## Main definitions

This file is intentionally kept small; many other constructions of, and lemmas about,
partial homeomorphisms can be found in other files under `Mathlib/Topology/PartialHomeomorph/`.

* `Homeomorph.toOpenPartialHomeomorph`: associating an open partial homeomorphism to a
  homeomorphism, with `source = target = Set.univ`;
* `OpenPartialHomeomorph.symm`: the inverse of an open partial homeomorphism

## Implementation notes

Most statements are copied from their `PartialEquiv` versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `PartialEquiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

structure OpenPartialHomeomorph (X : Type*) (Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] extends PartialEquiv X Y where
  open_source : IsOpen source
  open_target : IsOpen target
  continuousOn_toFun : ContinuousOn toFun source
  continuousOn_invFun : ContinuousOn invFun target

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-! Basic properties; inverse (symm instance) -/

section Basic
