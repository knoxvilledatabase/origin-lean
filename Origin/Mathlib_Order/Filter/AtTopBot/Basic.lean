/-
Extracted from Order/Filter/AtTopBot/Basic.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic results on `Filter.atTop` and `Filter.atBot` filters

In this file we prove many lemmas like “if `f → +∞`, then `f ± c → +∞`”.
-/

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

section IsDirected

variable [Preorder α] [IsDirectedOrder α] {p : α → Prop}

theorem hasAntitoneBasis_atTop [Nonempty α] : (@atTop α _).HasAntitoneBasis Ici :=
  .iInf_principal fun _ _ ↦ Ici_subset_Ici.2

theorem atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fun _ => True) Ici :=
  hasAntitoneBasis_atTop.1

lemma atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@atTop α _).HasBasis (fun _ => True) Ioi :=
  atTop_basis.to_hasBasis (fun a ha => ⟨a, ha, Ioi_subset_Ici_self⟩) fun a ha =>
    (exists_gt a).imp fun _b hb => ⟨ha, Ici_subset_Ioi.2 hb⟩

lemma atTop_basis_Ioi' [NoMaxOrder α] (a : α) : atTop.HasBasis (a < ·) Ioi := by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis_Ioi.to_hasBasis (fun b _ ↦ ?_) fun b _ ↦ ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  obtain ⟨d, hcd⟩ := exists_gt c
  exact ⟨d, hac.trans_lt hcd, Ioi_subset_Ioi (hbc.trans hcd.le)⟩

theorem atTop_basis' (a : α) : atTop.HasBasis (a ≤ ·) Ici := by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis.to_hasBasis (fun b _ ↦ ?_) fun b _ ↦ ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  exact ⟨c, hac, Ici_subset_Ici.2 hbc⟩

variable [Nonempty α]
