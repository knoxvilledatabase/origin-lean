/-
Extracted from Order/Interval/Set/OrdConnected.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Order-connected sets

We say that a set `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the
interval `[[x, y]]`. If `α` is a `DenselyOrdered` `ConditionallyCompleteLinearOrder` with
the `OrderTopology`, then this condition is equivalent to `IsPreconnected s`. If `α` is a
`LinearOrderedField`, then this condition is also equivalent to `Convex α s`.

In this file we prove that intersection of a family of `OrdConnected` sets is `OrdConnected` and
that all standard intervals are `OrdConnected`.
-/

open scoped Interval

open Set

open OrderDual (toDual ofDual)

namespace Set

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β] {s : Set α}

theorem ordConnected_def : OrdConnected s ↔ ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), Icc x y ⊆ s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem ordConnected_iff : OrdConnected s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≤ y → Icc x y ⊆ s :=
  ordConnected_def.trans
    ⟨fun hs _ hx _ hy _ => hs hx hy, fun H x hx y hy _ hz => H x hx y hy (le_trans hz.1 hz.2) hz⟩

theorem ordConnected_of_Ioo {α : Type*} [PartialOrder α] {s : Set α}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x < y → Ioo x y ⊆ s) : OrdConnected s := by
  rw [ordConnected_iff]
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with (rfl | hxy'); · simpa
  rw [← Ioc_insert_left hxy, ← Ioo_insert_right hxy']
  exact insert_subset_iff.2 ⟨hx, insert_subset_iff.2 ⟨hy, hs x hx y hy hxy'⟩⟩

theorem OrdConnected.preimage_mono {f : β → α} (hs : OrdConnected s) (hf : Monotone f) :
    OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hx hy ⟨hf hz.1, hf hz.2⟩⟩

theorem OrdConnected.preimage_anti {f : β → α} (hs : OrdConnected s) (hf : Antitone f) :
    OrdConnected (f ⁻¹' s) :=
  ⟨fun _ hx _ hy _ hz => hs.out hy hx ⟨hf hz.2, hf hz.1⟩⟩

protected theorem Icc_subset (s : Set α) [hs : OrdConnected s] {x y} (hx : x ∈ s) (hy : y ∈ s) :
    Icc x y ⊆ s :=
  hs.out hx hy

end Preorder

end Set

namespace OrderEmbedding

variable {α β : Type*} [Preorder α] [Preorder β]

theorem image_Icc (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Icc x y = Icc (e x) (e y) := by
  rw [← e.preimage_Icc, image_preimage_eq_inter_range, inter_eq_left.2 (he.out ⟨_, rfl⟩ ⟨_, rfl⟩)]

theorem image_Ico (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Ico x y = Ico (e x) (e y) := by
  rw [← e.preimage_Ico, image_preimage_eq_inter_range,
    inter_eq_left.2 <| Ico_subset_Icc_self.trans <| he.out ⟨_, rfl⟩ ⟨_, rfl⟩]

theorem image_Ioc (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Ioc x y = Ioc (e x) (e y) := by
  rw [← e.preimage_Ioc, image_preimage_eq_inter_range,
    inter_eq_left.2 <| Ioc_subset_Icc_self.trans <| he.out ⟨_, rfl⟩ ⟨_, rfl⟩]

theorem image_Ioo (e : α ↪o β) (he : OrdConnected (range e)) (x y : α) :
    e '' Ioo x y = Ioo (e x) (e y) := by
  rw [← e.preimage_Ioo, image_preimage_eq_inter_range,
    inter_eq_left.2 <| Ioo_subset_Icc_self.trans <| he.out ⟨_, rfl⟩ ⟨_, rfl⟩]

end OrderEmbedding

namespace Set

section Preorder

variable {α β : Type*} [Preorder α] [Preorder β]
