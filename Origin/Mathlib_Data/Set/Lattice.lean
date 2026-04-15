/-
Extracted from Data/Set/Lattice.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The set lattice

This file is a collection of results on the complete atomic Boolean algebra structure of `Set α`.
Notation for the complete lattice operations can be found in `Mathlib/Order/SetNotation.lean`.

## Main declarations
* `Set.sInter_eq_biInter`, `Set.sUnion_eq_biInter`: Shows that `⋂₀ s = ⋂ x ∈ s, x` and
  `⋃₀ s = ⋃ x ∈ s, x`.
* `Set.completeAtomicBooleanAlgebra`: `Set α` is a `CompleteAtomicBooleanAlgebra` with `≤ = ⊆`,
  `< = ⊂`, `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference.
  See `Set.instBooleanAlgebra`.
* `Set.unionEqSigmaOfDisjoint`: Equivalence between `⋃ i, t i` and `Σ i, t i`, where `t` is an
  indexed family of disjoint sets.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `iUnion`
* `⋂ i, s i` is called `iInter`
* `⋃ i j, s i j` is called `iUnion₂`. This is an `iUnion` inside an `iUnion`.
* `⋂ i j, s i j` is called `iInter₂`. This is an `iInter` inside an `iInter`.
* `⋃ i ∈ s, t i` is called `biUnion` for "bounded `iUnion`". This is the special case of `iUnion₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `biInter` for "bounded `iInter`". This is the special case of `iInter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `Set.iUnion`
* `⋂`: `Set.iInter`
* `⋃₀`: `Set.sUnion`
* `⋂₀`: `Set.sInter`
-/

open Function Set

universe u

variable {α β γ δ : Type*} {ι ι' ι₂ : Sort*} {κ κ₁ κ₂ : ι → Sort*} {κ' : ι' → Sort*}

namespace Set

/-! ### Complete lattice and complete Boolean algebra instances -/

theorem mem_iUnion₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋃ (i) (j), s i j) ↔ ∃ i j, x ∈ s i j := by
  simp_rw [mem_iUnion]

theorem mem_iInter₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋂ (i) (j), s i j) ↔ ∀ i j, x ∈ s i j := by
  simp_rw [mem_iInter]

theorem mem_iUnion_of_mem {s : ι → Set α} {a : α} (i : ι) (ha : a ∈ s i) : a ∈ ⋃ i, s i :=
  mem_iUnion.2 ⟨i, ha⟩

theorem mem_iUnion₂_of_mem {s : ∀ i, κ i → Set α} {a : α} {i : ι} (j : κ i) (ha : a ∈ s i j) :
    a ∈ ⋃ (i) (j), s i j :=
  mem_iUnion₂.2 ⟨i, j, ha⟩

theorem mem_iInter_of_mem {s : ι → Set α} {a : α} (h : ∀ i, a ∈ s i) : a ∈ ⋂ i, s i :=
  mem_iInter.2 h

theorem mem_iInter₂_of_mem {s : ∀ i, κ i → Set α} {a : α} (h : ∀ i j, a ∈ s i j) :
    a ∈ ⋂ (i) (j), s i j :=
  mem_iInter₂.2 h

/-! ### Union and intersection over an indexed family of sets -/
