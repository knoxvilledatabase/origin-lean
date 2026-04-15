/-
Extracted from Order/CompleteLattice/Finset.lean
Genuine: 24 of 31 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Lattice operations on finsets

This file is concerned with how big lattice or set operations behave when indexed by a finset.

See also `Mathlib/Data/Finset/Lattice/Fold.lean`, which is concerned with folding binary lattice
operations over a finset.
-/

assert_not_exists IsOrderedMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

section Lattice

variable {ι' : Sort*} [CompleteLattice α]

theorem iSup_eq_iSup_finset (s : ι → α) : ⨆ i, s i = ⨆ t : Finset ι, ⨆ i ∈ t, s i := by
  classical
  refine le_antisymm ?_ ?_
  · exact iSup_le fun b => le_iSup_of_le {b} <| le_iSup_of_le b <| le_iSup_of_le (by simp) <| le_rfl
  · exact iSup_le fun t => iSup_le fun b => iSup_le fun _ => le_iSup _ _

theorem iSup_eq_iSup_finset' (s : ι' → α) :
    ⨆ i, s i = ⨆ t : Finset (PLift ι'), ⨆ i ∈ t, s (PLift.down i) := by
  rw [← iSup_eq_iSup_finset, ← Equiv.plift.surjective.iSup_comp]; rfl

theorem iInf_eq_iInf_finset (s : ι → α) : ⨅ i, s i = ⨅ (t : Finset ι) (i ∈ t), s i :=
  @iSup_eq_iSup_finset αᵒᵈ _ _ _

theorem iInf_eq_iInf_finset' (s : ι' → α) :
    ⨅ i, s i = ⨅ t : Finset (PLift ι'), ⨅ i ∈ t, s (PLift.down i) :=
  @iSup_eq_iSup_finset' αᵒᵈ _ _ _

end Lattice

namespace Set

variable {ι' : Sort*}

theorem iUnion_eq_iUnion_finset (s : ι → Set α) : ⋃ i, s i = ⋃ t : Finset ι, ⋃ i ∈ t, s i :=
  iSup_eq_iSup_finset s

theorem iUnion_eq_iUnion_finset' (s : ι' → Set α) :
    ⋃ i, s i = ⋃ t : Finset (PLift ι'), ⋃ i ∈ t, s (PLift.down i) :=
  iSup_eq_iSup_finset' s

theorem iInter_eq_iInter_finset (s : ι → Set α) : ⋂ i, s i = ⋂ t : Finset ι, ⋂ i ∈ t, s i :=
  iInf_eq_iInf_finset s

theorem iInter_eq_iInter_finset' (s : ι' → Set α) :
    ⋂ i, s i = ⋂ t : Finset (PLift ι'), ⋂ i ∈ t, s (PLift.down i) :=
  iInf_eq_iInf_finset' s

theorem iUnion_finset_eq_set (s : Set ι) :
    ⋃ s' : Finset s, Subtype.val '' (s' : Set s) = s := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, Subtype.exists,
    exists_and_right, exists_eq_right]
  exact ⟨fun ⟨_, hx, _⟩ ↦ hx, fun hx ↦ ⟨{⟨x, hx⟩}, hx, by simp⟩⟩

end Set

namespace Finset

section minimal

variable [DecidableEq α] {P : Finset α → Prop} {s : Finset α}

theorem maximal_iff_forall_insert (hP : ∀ ⦃s t⦄, P t → s ⊆ t → P s) :
    Maximal P s ↔ P s ∧ ∀ x ∉ s, ¬ P (insert x s) := by
  simp only [Maximal, and_congr_right_iff]
  exact fun _ ↦ ⟨fun h x hxs hx ↦ hxs <| h hx (subset_insert _ _) (mem_insert_self x s),
    fun h t ht hst x hxt ↦ by_contra fun hxs ↦ h x hxs (hP ht (insert_subset hxt hst))⟩

theorem minimal_iff_forall_diff_singleton (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) :
    Minimal P s ↔ P s ∧ ∀ x ∈ s, ¬ P (s.erase x) where
  mp h := ⟨h.prop, fun x hxs hx ↦ by simpa using h.le_of_le hx (erase_subset _ _) hxs⟩
  mpr h := ⟨h.1, fun t ht hts x hxs ↦ by_contra fun hxt ↦
    h.2 x hxs <| hP ht (subset_erase.2 ⟨hts, hxt⟩)⟩

end minimal

/-! ### Interaction with big lattice/set operations -/

section Lattice

variable [CompleteLattice β]

theorem iInf_option_toFinset (o : Option α) (f : α → β) : ⨅ x ∈ o.toFinset, f x = ⨅ x ∈ o, f x :=
  @iSup_option_toFinset _ βᵒᵈ _ _ _

variable [DecidableEq α]

theorem iSup_union {f : α → β} {s t : Finset α} :
    ⨆ x ∈ s ∪ t, f x = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x := by simp [iSup_or, iSup_sup_eq]

theorem iInf_union {f : α → β} {s t : Finset α} :
    ⨅ x ∈ s ∪ t, f x = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @iSup_union α βᵒᵈ _ _ _ _ _

theorem iSup_insert (a : α) (s : Finset α) (t : α → β) :
    ⨆ x ∈ insert a s, t x = t a ⊔ ⨆ x ∈ s, t x := by
  rw [insert_eq]
  simp only [iSup_union, Finset.iSup_singleton]

theorem iInf_insert (a : α) (s : Finset α) (t : α → β) :
    ⨅ x ∈ insert a s, t x = t a ⊓ ⨅ x ∈ s, t x :=
  @iSup_insert α βᵒᵈ _ _ _ _ _

theorem iSup_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    ⨆ x ∈ s.image f, g x = ⨆ y ∈ s, g (f y) := by rw [← iSup_coe, coe_image, iSup_image, iSup_coe]

theorem iInf_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    ⨅ x ∈ s.image f, g x = ⨅ y ∈ s, g (f y) := by rw [← iInf_coe, coe_image, iInf_image, iInf_coe]

theorem iSup_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    ⨆ i ∈ insert x t, Function.update f x s i = s ⊔ ⨆ i ∈ t, f i := by
  simp only [Finset.iSup_insert, update_self]
  rcongr (i hi); apply update_of_ne; rintro rfl; exact hx hi

theorem iInf_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    ⨅ i ∈ insert x t, update f x s i = s ⊓ ⨅ i ∈ t, f i :=
  @iSup_insert_update α βᵒᵈ _ _ _ _ f _ hx

theorem iSup_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    ⨆ y ∈ s.biUnion t, f y = ⨆ (x ∈ s) (y ∈ t x), f y := by simp [@iSup_comm _ α, iSup_and]

theorem iInf_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    ⨅ y ∈ s.biUnion t, f y = ⨅ (x ∈ s) (y ∈ t x), f y :=
  @iSup_biUnion _ βᵒᵈ _ _ _ _ _ _

end Lattice

theorem set_biUnion_singleton (a : α) (s : α → Set β) : ⋃ x ∈ ({a} : Finset α), s x = s a :=
  iSup_singleton a s

theorem set_biInter_singleton (a : α) (s : α → Set β) : ⋂ x ∈ ({a} : Finset α), s x = s a :=
  iInf_singleton a s
