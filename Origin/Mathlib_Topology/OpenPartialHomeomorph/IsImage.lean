/-
Extracted from Topology/OpenPartialHomeomorph/IsImage.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Partial homeomorphisms: Images of sets

## Main definitions

* `OpenPartialHomeomorph.IsImage`: predicate for when one set is an image of another
* `OpenPartialHomeomorph.ofSet`: the identity on a set `s`
* `OpenPartialHomeomorph.EqOnSource`: equivalence relation describing the "right" notion of equality
  for open partial homeomorphisms

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

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

section IsImage

/-!
## `OpenPartialHomeomorph.IsImage` relation

We say that `t : Set Y` is an image of `s : Set X` under an open partial homeomorphism `e` if any of
the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `PartialEquiv.IsImage` for open partial homeomorphisms.
In this section we transfer API about `PartialEquiv.IsImage` to open partial homeomorphisms and
add a few `OpenPartialHomeomorph`-specific lemmas like `OpenPartialHomeomorph.IsImage.closure`.
-/

def IsImage (s : Set X) (t : Set Y) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set X} {t : Set Y} {x : X} {y : Y}
