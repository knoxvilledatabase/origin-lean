/-
Extracted from Combinatorics/SimpleGraph/Regularity/Equitabilise.lean
Genuine: 5 of 9 | Dissolved: 3 | Infrastructure: 1
-/
import Origin.Core

/-!
# Equitabilising a partition

This file allows to blow partitions up into parts of controlled size. Given a partition `P` and
`a b m : ℕ`, we want to find a partition `Q` with `a` parts of size `m` and `b` parts of size
`m + 1` such that all parts of `P` are "as close as possible" to unions of parts of `Q`. By
"as close as possible", we mean that each part of `P` can be written as the union of some parts of
`Q` along with at most `m` other elements.

## Main declarations

* `Finpartition.equitabilise`: `P.equitabilise h` where `h : a * m + b * (m + 1)` is a partition
  with `a` parts of size `m` and `b` parts of size `m + 1` which almost refines `P`.
* `Finpartition.exists_equipartition_card_eq`: We can find equipartitions of arbitrary size.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

open Finset Nat

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s t : Finset α} {m n a b : ℕ} {P : Finpartition s}

variable (h : a * m + b * (m + 1) = #s)

noncomputable def equitabilise : Finpartition s :=
  (P.equitabilise_aux h).choose

variable {h}

theorem card_eq_of_mem_parts_equitabilise :
    t ∈ (P.equitabilise h).parts → #t = m ∨ #t = m + 1 :=
  (P.equitabilise_aux h).choose_spec.1 _

theorem equitabilise_isEquipartition : (P.equitabilise h).IsEquipartition :=
  Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨m, fun _ => card_eq_of_mem_parts_equitabilise⟩

variable (P h)

theorem card_filter_equitabilise_big : #{u ∈ (P.equitabilise h).parts | #u = m + 1} = b :=
  (P.equitabilise_aux h).choose_spec.2.2

-- DISSOLVED: card_filter_equitabilise_small

-- DISSOLVED: card_parts_equitabilise

theorem card_parts_equitabilise_subset_le :
    t ∈ P.parts → #(t \ {u ∈ (P.equitabilise h).parts | u ⊆ t}.biUnion id) ≤ m :=
  (Classical.choose_spec <| P.equitabilise_aux h).2.1 t

variable (s)

-- DISSOLVED: exists_equipartition_card_eq

end Finpartition
