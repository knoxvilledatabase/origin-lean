/-
Extracted from Order/Filter/Cofinite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The cofinite filter

In this file we define

`Filter.cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `Filter.atTop`.

## TODO

Define filters for other cardinalities of the complement.
-/

open Set Function

variable {ι α β : Type*} {l : Filter α}

namespace Filter

def cofinite : Filter α :=
  comk Set.Finite finite_empty (fun _t ht _s hsub ↦ ht.subset hsub) fun _ h _ ↦ h.union
