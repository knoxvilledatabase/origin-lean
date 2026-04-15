/-
Extracted from Topology/Algebra/Valued/NormedValued.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Correspondence between nontrivial nonarchimedean norms and rank one valuations

Nontrivial nonarchimedean norms correspond to rank one valuations.

## Main Definitions
* `NormedField.toValued` : the valued field structure on a nonarchimedean normed field `K`,
  determined by the norm.
* `Valued.toNormedField` : the normed field structure determined by a rank one valuation.

## Main Results
* The valuation of a normed field has rank at most one.

## Tags

norm, nonarchimedean, nontrivial, valuation, rank one
-/

noncomputable section

open Filter Set Valuation MonoidWithZeroHom

open scoped NNReal

variable {K : Type*} [hK : NormedField K] [IsUltrametricDist K]

namespace NormedField

set_option linter.style.whitespace false in -- manual alignment is not recognised

def valuation : Valuation K ℝ≥0 where
  toFun           := nnnorm
  map_zero'       := nnnorm_zero
  map_one'        := nnnorm_one
  map_mul'        := nnnorm_mul
  map_add_le_max' := IsUltrametricDist.norm_add_le_max
