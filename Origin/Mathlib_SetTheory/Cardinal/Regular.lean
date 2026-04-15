/-
Extracted from SetTheory/Cardinal/Regular.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Regular cardinals

This file defines regular and inaccessible cardinals.

## Main definitions

* `Cardinal.IsRegular c` means that `c` is a regular cardinal: `ℵ₀ ≤ c ∧ c.ord.cof = c`.
* `Cardinal.IsInaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c`.

## TODO

* Prove more theorems on inaccessible cardinals.
* Define singular cardinals.
-/

universe u v

open Function Cardinal Set Order Ordinal

namespace Cardinal

/-! ### Regular cardinals -/

structure IsRegular (c : Cardinal) : Prop where
  /-- A regular cardinal is infinite. -/
  aleph0_le : ℵ₀ ≤ c
  /-- A cardinal equals its own cofinality. See `IsRegular.cof_eq`. -/
  le_cof_ord : c ≤ c.ord.cof

theorem IsRegular.cof_ord {c : Cardinal} (H : c.IsRegular) : c.ord.cof = c :=
  (cof_ord_le c).antisymm H.2
