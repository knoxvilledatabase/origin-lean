/-
Extracted from Logic/Small/Set.lean
Genuine: 8 of 27 | Dissolved: 0 | Infrastructure: 19
-/
import Origin.Core

/-!
# Results about `Small` on coerced sets
-/

universe u u1 u2 u3 u4

variable {α : Type u1} {β : Type u2} {γ : Type u3} {ι : Type u4}

theorem small_subset {s t : Set α} (hts : t ⊆ s) [Small.{u} s] : Small.{u} t :=
  small_of_injective (Set.inclusion_injective hts)

-- INSTANCE (free from Core): small_powerset

-- INSTANCE (free from Core): small_setProd

-- INSTANCE (free from Core): small_setPi

-- INSTANCE (free from Core): small_range

-- INSTANCE (free from Core): small_image

-- INSTANCE (free from Core): small_image2

theorem small_univ_iff : Small.{u} (@Set.univ α) ↔ Small.{u} α :=
  small_congr <| Equiv.Set.univ α

-- INSTANCE (free from Core): small_univ

-- INSTANCE (free from Core): small_union

-- INSTANCE (free from Core): small_iUnion

-- INSTANCE (free from Core): small_sUnion

-- INSTANCE (free from Core): small_biUnion

-- INSTANCE (free from Core): small_insert

-- INSTANCE (free from Core): small_diff

-- INSTANCE (free from Core): small_sep

-- INSTANCE (free from Core): small_inter_of_left

-- INSTANCE (free from Core): small_inter_of_right

theorem small_iInter (s : ι → Set α) (i : ι)
    [Small.{u} (s i)] : Small.{u} (⋂ i, s i) :=
  small_subset (Set.iInter_subset s i)

-- INSTANCE (free from Core): small_iInter'

theorem small_sInter {s : Set (Set α)} {t : Set α} (ht : t ∈ s)
    [Small.{u} t] : Small.{u} (⋂₀ s) :=
  Set.sInter_eq_iInter ▸ small_iInter _ ⟨t, ht⟩

-- INSTANCE (free from Core): small_sInter'

theorem small_biInter {s : Set ι} {i : ι} (hi : i ∈ s)
    (f : (i : ι) → i ∈ s → Set α) [Small.{u} (f i hi)] : Small.{u} (⋂ i, ⋂ hi, f i hi) :=
  Set.biInter_eq_iInter s f ▸ small_iInter _ ⟨i, hi⟩

-- INSTANCE (free from Core): small_biInter'

theorem small_empty : Small.{u} (∅ : Set α) :=
  inferInstance

theorem small_single (x : α) : Small.{u} ({x} : Set α) :=
  inferInstance

theorem small_pair (x y : α) : Small.{u} ({x, y} : Set α) :=
  inferInstance
