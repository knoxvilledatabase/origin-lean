/-
Extracted from Order/Filter/Cocardinal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The cocardinal filter

In this file we define `Filter.cocardinal hc`: the filter of sets with cardinality less than
  a regular cardinal `c` that satisfies `Cardinal.aleph0 < c`.
  Such filters are `CardinalInterFilter` with cardinality `c`.

-/

open Set Filter Cardinal

universe u

variable {α : Type u} {c : Cardinal.{u}} {hreg : c.IsRegular}

namespace Filter

variable (α) in

def cocardinal (hreg : c.IsRegular) : Filter α := by
  apply ofCardinalUnion {s | Cardinal.mk s < c} (natCast_lt_aleph0.trans_le hreg.aleph0_le)
  · refine fun s hS hSc ↦ lt_of_le_of_lt (mk_sUnion_le _) <| mul_lt_of_lt hreg.aleph0_le hS ?_
    apply iSup_lt_of_lt_cof_ord _ fun i ↦ hSc i.1 i.2
    rwa [hreg.cof_ord]
  · exact fun _ hSc _ ht ↦ lt_of_le_of_lt (mk_le_mk_of_subset ht) hSc
