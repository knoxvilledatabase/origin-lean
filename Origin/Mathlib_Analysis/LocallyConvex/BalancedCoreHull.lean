/-
Extracted from Analysis/LocallyConvex/BalancedCoreHull.lean
Genuine: 13 of 13 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Balanced Core and Balanced Hull

## Main definitions

* `balancedCore`: The largest balanced subset of a set `s`.
* `balancedHull`: The smallest balanced superset of a set `s`.

## Main statements

* `balancedCore_eq_iInter`: Characterization of the balanced core as an intersection over subsets.
* `nhds_basis_closed_balanced`: The closed balanced sets form a basis of the neighborhood filter.

## Implementation details

The balanced core and hull are implemented differently: for the core we take the obvious definition
of the union over all balanced sets that are contained in `s`, whereas for the hull, we take the
union over `r • s`, for `r` the scalars with `‖r‖ ≤ 1`. We show that `balancedHull` has the
defining properties of a hull in `Balanced.balancedHull_subset_of_subset` and `subset_balancedHull`.
For the core we need slightly stronger assumptions to obtain a characterization as an intersection,
this is `balancedCore_eq_iInter`.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

balanced
-/

open Set Pointwise Topology Filter

variable {𝕜 E ι : Type*}

section balancedHull

section SeminormedRing

variable [SeminormedRing 𝕜]

section SMul

variable (𝕜) [SMul 𝕜 E] {s t : Set E} {x : E}

def balancedCore (s : Set E) :=
  ⋃₀ { t : Set E | Balanced 𝕜 t ∧ t ⊆ s }

def balancedCoreAux (s : Set E) :=
  ⋂ (r : 𝕜) (_ : 1 ≤ ‖r‖), r • s

def balancedHull (s : Set E) :=
  ⋃ (r : 𝕜) (_ : ‖r‖ ≤ 1), r • s

variable {𝕜}

theorem balancedCore_subset (s : Set E) : balancedCore 𝕜 s ⊆ s :=
  sUnion_subset fun _ ht => ht.2

theorem balancedCore_empty : balancedCore 𝕜 (∅ : Set E) = ∅ :=
  eq_empty_of_subset_empty (balancedCore_subset _)

theorem mem_balancedCore_iff : x ∈ balancedCore 𝕜 s ↔ ∃ t, Balanced 𝕜 t ∧ t ⊆ s ∧ x ∈ t := by
  simp_rw [balancedCore, mem_sUnion, mem_setOf_eq, and_assoc]

theorem smul_balancedCore_subset (s : Set E) {a : 𝕜} (ha : ‖a‖ ≤ 1) :
    a • balancedCore 𝕜 s ⊆ balancedCore 𝕜 s := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_balancedCore_iff] at hy
  rcases hy with ⟨t, ht1, ht2, hy⟩
  exact ⟨t, ⟨ht1, ht2⟩, ht1 a ha (smul_mem_smul_set hy)⟩

theorem balancedCore_balanced (s : Set E) : Balanced 𝕜 (balancedCore 𝕜 s) := fun _ =>
  smul_balancedCore_subset s

theorem Balanced.subset_balancedCore_of_subset (hs : Balanced 𝕜 s) (h : s ⊆ t) :
    s ⊆ balancedCore 𝕜 t :=
  subset_sUnion_of_mem ⟨hs, h⟩

lemma Balanced.balancedCore_eq (h : Balanced 𝕜 s) : balancedCore 𝕜 s = s :=
  le_antisymm (balancedCore_subset _) (h.subset_balancedCore_of_subset subset_rfl)

theorem mem_balancedCoreAux_iff : x ∈ balancedCoreAux 𝕜 s ↔ ∀ r : 𝕜, 1 ≤ ‖r‖ → x ∈ r • s :=
  mem_iInter₂

theorem mem_balancedHull_iff : x ∈ balancedHull 𝕜 s ↔ ∃ r : 𝕜, ‖r‖ ≤ 1 ∧ x ∈ r • s := by
  simp [balancedHull]

theorem Balanced.balancedHull_subset_of_subset (ht : Balanced 𝕜 t) (h : s ⊆ t) :
    balancedHull 𝕜 s ⊆ t := by
  intro x hx
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 hx
  exact ht.smul_mem hr (h hy)
