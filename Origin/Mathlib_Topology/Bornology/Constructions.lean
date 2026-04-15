/-
Extracted from Topology/Bornology/Constructions.lean
Genuine: 20 of 34 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core

/-!
# Bornology structure on products and subtypes

In this file we define `Bornology` and `BoundedSpace` instances on `α × β`, `Π i, X i`, and
`{x // p x}`. We also prove basic lemmas about `Bornology.cobounded` and `Bornology.IsBounded`
on these types.
-/

open Set Filter Bornology Function

open Filter

variable {α β ι : Type*} {X : ι → Type*} [Bornology α] [Bornology β]
  [∀ i, Bornology (X i)]

-- INSTANCE (free from Core): Prod.instBornology

-- INSTANCE (free from Core): Pi.instBornology

abbrev Bornology.induced {α β : Type*} [Bornology β] (f : α → β) : Bornology α where
  cobounded := comap f (cobounded β)
  le_cofinite := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)

-- INSTANCE (free from Core): {p

namespace Bornology

/-!
### Bounded sets in `α × β`
-/

theorem isBounded_image_fst_and_snd {s : Set (α × β)} :
    IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded s :=
  compl_mem_coprod.symm

lemma IsBounded.image_fst {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.fst '' s) :=
  (isBounded_image_fst_and_snd.2 hs).1

lemma IsBounded.image_snd {s : Set (α × β)} (hs : IsBounded s) : IsBounded (Prod.snd '' s) :=
  (isBounded_image_fst_and_snd.2 hs).2

variable {s : Set α} {t : Set β} {S : ∀ i, Set (X i)}

theorem IsBounded.fst_of_prod (h : IsBounded (s ×ˢ t)) (ht : t.Nonempty) : IsBounded s :=
  fst_image_prod s ht ▸ h.image_fst

theorem IsBounded.snd_of_prod (h : IsBounded (s ×ˢ t)) (hs : s.Nonempty) : IsBounded t :=
  snd_image_prod hs t ▸ h.image_snd

theorem IsBounded.prod (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ×ˢ t) :=
  isBounded_image_fst_and_snd.1
    ⟨hs.subset <| fst_image_prod_subset _ _, ht.subset <| snd_image_prod_subset _ _⟩

theorem isBounded_prod_of_nonempty (hne : Set.Nonempty (s ×ˢ t)) :
    IsBounded (s ×ˢ t) ↔ IsBounded s ∧ IsBounded t :=
  ⟨fun h => ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, fun h => h.1.prod h.2⟩

theorem isBounded_prod : IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBounded t := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht); · simp
  simp only [hs.ne_empty, ht.ne_empty, isBounded_prod_of_nonempty (hs.prod ht), false_or]

theorem isBounded_prod_self : IsBounded (s ×ˢ s) ↔ IsBounded s := by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  exact (isBounded_prod_of_nonempty (hs.prod hs)).trans and_self_iff

/-!
### Bounded sets in `Π i, X i`
-/

theorem forall_isBounded_image_eval_iff {s : Set (∀ i, X i)} :
    (∀ i, IsBounded (eval i '' s)) ↔ IsBounded s :=
  compl_mem_coprodᵢ.symm

lemma IsBounded.image_eval {s : Set (∀ i, X i)} (hs : IsBounded s) (i : ι) :
    IsBounded (eval i '' s) :=
  forall_isBounded_image_eval_iff.2 hs i

theorem IsBounded.pi (h : ∀ i, IsBounded (S i)) : IsBounded (pi univ S) :=
  forall_isBounded_image_eval_iff.1 fun i => (h i).subset eval_image_univ_pi_subset

theorem isBounded_pi_of_nonempty (hne : (pi univ S).Nonempty) :
    IsBounded (pi univ S) ↔ ∀ i, IsBounded (S i) :=
  ⟨fun H i => @eval_image_univ_pi _ _ _ i hne ▸ forall_isBounded_image_eval_iff.2 H i, IsBounded.pi⟩

theorem isBounded_pi : IsBounded (pi univ S) ↔ (∃ i, S i = ∅) ∨ ∀ i, IsBounded (S i) := by
  by_cases hne : ∃ i, S i = ∅
  · simp [hne, univ_pi_eq_empty_iff.2 hne]
  · simp only [hne, false_or]
    simp only [not_exists, ← nonempty_iff_ne_empty, ← univ_pi_nonempty_iff] at hne
    exact isBounded_pi_of_nonempty hne

/-!
### Bounded sets in `{x // p x}`
-/

theorem isBounded_induced {α β : Type*} [Bornology β] {f : α → β} {s : Set α} :
    @IsBounded α (Bornology.induced f) s ↔ IsBounded (f '' s) :=
  compl_mem_comap

theorem isBounded_image_subtype_val {p : α → Prop} {s : Set { x // p x }} :
    IsBounded (Subtype.val '' s) ↔ IsBounded s :=
  isBounded_induced.symm

end Bornology

/-!
### Bounded spaces
-/

open Bornology

-- INSTANCE (free from Core): [BoundedSpace

-- INSTANCE (free from Core): [∀

theorem boundedSpace_induced_iff {α β : Type*} [Bornology β] {f : α → β} :
    @BoundedSpace α (Bornology.induced f) ↔ IsBounded (range f) := by
  rw [← @isBounded_univ, isBounded_induced, image_univ]

theorem boundedSpace_subtype_iff {p : α → Prop} :
    BoundedSpace (Subtype p) ↔ IsBounded { x | p x } := by
  rw [boundedSpace_induced_iff, Subtype.range_coe_subtype]

theorem boundedSpace_val_set_iff {s : Set α} : BoundedSpace s ↔ IsBounded s :=
  boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_subtype⟩ := boundedSpace_subtype_iff

alias ⟨_, Bornology.IsBounded.boundedSpace_val⟩ := boundedSpace_val_set_iff

-- INSTANCE (free from Core): [BoundedSpace

/-!
### `Additive`, `Multiplicative`

The bornology on those type synonyms is inherited without change.
-/

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [BoundedSpace

-- INSTANCE (free from Core): [BoundedSpace

/-!
### Order dual

The bornology on this type synonym is inherited without change.
-/

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [BoundedSpace
