/-
Extracted from RingTheory/HahnSeries/Cardinal.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cardinality of Hahn series

We define `HahnSeries.cardSupp` as the cardinality of the support of a Hahn series, and find bounds
for the cardinalities of different operations. We also build the subgroups, subrings, etc. of Hahn
series bounded by a given infinite cardinal.
-/

open Cardinal

namespace HahnSeries

variable {Γ R S α : Type*}

/-! ### Cardinality function -/

section PartialOrder

variable [PartialOrder Γ]

section Zero

variable [Zero R]

def cardSupp (x : R⟦Γ⟧) : Cardinal :=
  #x.support

theorem cardSupp_congr [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support = y.support) :
    x.cardSupp = y.cardSupp := by
  simp_rw [cardSupp, h]

theorem cardSupp_mono [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support ⊆ y.support) :
    x.cardSupp ≤ y.cardSupp :=
  mk_le_mk_of_subset h
