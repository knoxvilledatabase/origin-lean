/-
Extracted from SetTheory/ZFC/Cardinal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cardinalities of ZFC sets

In this file, we define the cardinalities of ZFC sets as `ZFSet.{u} → Cardinal.{u}`.

## Definitions

* `ZFSet.card`: Cardinality of a ZFC set.
-/

universe u v

open Cardinal

namespace ZFSet

def card (x : ZFSet.{u}) : Cardinal.{u} := #(Shrink x)

variable {x y : ZFSet.{u}}

theorem cardinalMk_coe_sort : #x = lift.{u + 1, u} (card x) := by
  rw [card, lift_mk_shrink'']
