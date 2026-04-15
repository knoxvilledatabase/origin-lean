/-
Extracted from Order/SupIndep.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

## Main definitions

* `Finset.SupIndep s f`: a family of elements `f` are supremum independent on the finite set `s`.
* `sSupIndep s`: a set of elements are supremum independent.
* `iSupIndep f`: a family of elements are supremum independent.

## Main statements

* In a distributive lattice, supremum independence is equivalent to pairwise disjointness:
  * `Finset.supIndep_iff_pairwiseDisjoint`
  * `CompleteLattice.sSupIndep_iff_pairwiseDisjoint`
  * `CompleteLattice.iSupIndep_iff_pairwiseDisjoint`
* Otherwise, supremum independence is stronger than pairwise disjointness:
  * `Finset.SupIndep.pairwiseDisjoint`
  * `sSupIndep.pairwiseDisjoint`
  * `iSupIndep.pairwiseDisjoint`

## Implementation notes

For the finite version, we avoid the "obvious" definition
`∀ i ∈ s, Disjoint (f i) ((s.erase i).sup f)` because `erase` would require decidable equality on
`ι`.
-/

variable {α β ι ι' : Type*}

/-! ### On lattices with a bottom element, via `Finset.sup` -/

namespace Finset

section Lattice

variable [Lattice α] [OrderBot α]

def SupIndep (s : Finset ι) (f : ι → α) : Prop :=
  ∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → Disjoint (f i) (t.sup f)

variable {s t : Finset ι} {f g : ι → α} {i : ι}

theorem supIndep_iff_disjoint_erase [DecidableEq ι] :
    s.SupIndep f ↔ ∀ i ∈ s, Disjoint (f i) ((s.erase i).sup f) :=
  ⟨fun hs _ hi => hs (erase_subset _ _) hi (notMem_erase _ _), fun hs _ ht i hi hit =>
    (hs i hi).mono_right (sup_mono fun _ hj => mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

-- INSTANCE (free from Core): [DecidableEq

theorem SupIndep.subset (ht : t.SupIndep f) (h : s ⊆ t) : s.SupIndep f := fun _ hu _ hi =>
  ht (hu.trans h) (h hi)

lemma SupIndep.mono (hf : s.SupIndep f) (h : ∀ i ∈ s, g i ≤ f i) : s.SupIndep g :=
  fun _ ht j hj htj ↦ (hf ht hj htj).mono (h j hj) (sup_mono_fun fun b a ↦ h b (ht a))
