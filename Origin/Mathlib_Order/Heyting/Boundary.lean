/-
Extracted from Order/Heyting/Boundary.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Co-Heyting boundary

The boundary of an element of a co-Heyting algebra is the intersection of its Heyting negation with
itself. The boundary in the co-Heyting algebra of closed sets coincides with the topological
boundary.

## Main declarations

* `Coheyting.boundary`: Co-Heyting boundary. `Coheyting.boundary a = a ⊓ ￢a`

## Notation

`∂ a` is notation for `Coheyting.boundary a` in scope `Heyting`.
-/

assert_not_exists RelIso

variable {α : Type*}

namespace Coheyting

variable [CoheytingAlgebra α] {a b : α}

def boundary (a : α) : α :=
  a ⊓ ￢a

scoped[Heyting] prefix:120 "∂ " => Coheyting.boundary

open Heyting

theorem boundary_le : ∂ a ≤ a :=
  inf_le_left

theorem boundary_le_hnot : ∂ a ≤ ￢a :=
  inf_le_right
