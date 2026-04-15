/-
Extracted from Order/WellQuasiOrder.lean
Genuine: 7 of 9 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Well quasi-orders

A well quasi-order (WQO) is a relation such that any infinite sequence contains an infinite
subsequence of related elements. For a preorder, this is equivalent to having a well-founded order
with no infinite antichains.

## Main definitions

* `WellQuasiOrdered`: a predicate for WQO unbundled relations
* `WellQuasiOrderedLE`: a typeclass for a bundled WQO `≤` relation

## Tags

wqo, pwo, well quasi-order, partial well order, dickson order
-/

variable {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}

def WellQuasiOrdered (r : α → α → Prop) : Prop :=
  ∀ f : ℕ → α, ∃ m n : ℕ, m < n ∧ r (f m) (f n)

theorem wellQuasiOrdered_of_isEmpty [IsEmpty α] (r : α → α → Prop) : WellQuasiOrdered r :=
  fun f ↦ isEmptyElim (f 0)

theorem IsAntichain.finite_of_wellQuasiOrdered {s : Set α} (hs : IsAntichain r s)
    (hr : WellQuasiOrdered r) : s.Finite := by
  by_contra! hi
  obtain ⟨m, n, hmn, h⟩ := hr fun n => hi.natEmbedding _ n
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    hs.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)

theorem Finite.wellQuasiOrdered (r : α → α → Prop) [Finite α] [Std.Refl r] :
    WellQuasiOrdered r := by
  intro f
  obtain ⟨m, n, h, hf⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem (f := f)
    fun _ ↦ Set.mem_univ _
  exact ⟨m, n, h, hf ▸ refl _⟩

theorem WellQuasiOrdered.prod [IsPreorder α r] (hr : WellQuasiOrdered r) (hs : WellQuasiOrdered s) :
    WellQuasiOrdered fun a b : α × β ↦ r a.1 b.1 ∧ s a.2 b.2 := by
  intro f
  obtain ⟨g, h₁⟩ := hr.exists_monotone_subseq (Prod.fst ∘ f)
  obtain ⟨m, n, h, hf⟩ := hs (Prod.snd ∘ f ∘ g)
  exact ⟨g m, g n, g.strictMono h, h₁ _ _ h.le, hf⟩

theorem WellQuasiOrdered.pi {ι : Type*} {α : ι → Type*} [Finite ι] {r : ∀ i, (α i → α i → Prop)}
    [∀ i, IsPreorder (α i) (r i)] (hr : ∀ i, WellQuasiOrdered (r i)) :
    WellQuasiOrdered fun a b : ∀ i, α i => ∀ i, r i (a i) (b i) := by
  haveI := Fintype.ofFinite ι
  haveI : IsPreorder (∀ i, α i) (fun a b : ∀ i, α i => ∀ i, r i (a i) (b i)) :=
    { refl a i := refl (a i)
      trans a b c hab hbc i := _root_.trans (hab i) (hbc i) }
  suffices ∀ (s : Finset ι) (f : ℕ → ∀ i, α i),
    ∃ g : ℕ ↪o ℕ, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ i, i ∈ s → r i ((f ∘ g) a i) ((f ∘ g) b i) by
    rw [wellQuasiOrdered_iff_exists_monotone_subseq]
    intro f
    simpa only [Finset.mem_univ, true_imp_iff] using this Finset.univ f
  refine Finset.cons_induction ?_ ?_
  · intro f
    exists RelEmbedding.refl (· ≤ ·)
    simp only [IsEmpty.forall_iff, imp_true_iff, Finset.notMem_empty]
  · intro i s hi ih f
    obtain ⟨g, hg⟩ := (hr i).exists_monotone_subseq (f · i)
    obtain ⟨g', hg'⟩ := ih (f ∘ g)
    refine ⟨g'.trans g, fun a b hab => (Finset.forall_mem_cons _ _).2 ?_⟩
    exact ⟨hg _ _ (OrderHomClass.mono g' hab), hg' hab⟩

theorem RelIso.wellQuasiOrdered_iff {α β} {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) :
    WellQuasiOrdered r ↔ WellQuasiOrdered s := by
  apply (Equiv.arrowCongr (.refl ℕ) f).forall_congr
  congr! with g a b
  simp [f.map_rel_iff]
