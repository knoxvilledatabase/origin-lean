/-
Extracted from Topology/NhdsSet.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Neighborhoods of a set

In this file we define the filter `𝓝ˢ s` or `nhdsSet s` consisting of all neighborhoods of a set
`s`.

## Main Properties

There are a couple different notions equivalent to `s ∈ 𝓝ˢ t`:
* `s ⊆ interior t` using `subset_interior_iff_mem_nhdsSet`
* `∀ x : X, x ∈ t → s ∈ 𝓝 x` using `mem_nhdsSet_iff_forall`
* `∃ U : Set X, IsOpen U ∧ t ⊆ U ∧ U ⊆ s` using `mem_nhdsSet_iff_exists`

Furthermore, we have the following results:
* `monotone_nhdsSet`: `𝓝ˢ` is monotone
* In T₁-spaces, `𝓝ˢ` is strictly monotone and hence injective:
  `strict_mono_nhdsSet`/`injective_nhdsSet`. These results are in
  `Mathlib/Topology/Separation/Basic.lean`.
-/

open Set Filter Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Filter X}
  {s t s₁ s₂ t₁ t₂ : Set X} {x : X}

theorem nhdsSet_diagonal (X) [TopologicalSpace (X × X)] :
    𝓝ˢ (diagonal X) = ⨆ (x : X), 𝓝 (x, x) := by
  rw [nhdsSet, ← range_diag, ← range_comp]
  rfl

theorem mem_nhdsSet_iff_forall : s ∈ 𝓝ˢ t ↔ ∀ x : X, x ∈ t → s ∈ 𝓝 x := by
  simp_rw [nhdsSet, Filter.mem_sSup, forall_mem_image]

lemma nhdsSet_le : 𝓝ˢ s ≤ f ↔ ∀ x ∈ s, 𝓝 x ≤ f := by simp [nhdsSet]

theorem bUnion_mem_nhdsSet {t : X → Set X} (h : ∀ x ∈ s, t x ∈ 𝓝 x) : (⋃ x ∈ s, t x) ∈ 𝓝ˢ s :=
  mem_nhdsSet_iff_forall.2 fun x hx => mem_of_superset (h x hx) <|
    subset_iUnion₂ (s := fun x _ => t x) x hx

theorem subset_interior_iff_mem_nhdsSet : s ⊆ interior t ↔ t ∈ 𝓝ˢ s := by
  simp_rw [mem_nhdsSet_iff_forall, subset_interior_iff_nhds]

theorem disjoint_principal_nhdsSet : Disjoint (𝓟 s) (𝓝ˢ t) ↔ Disjoint (closure s) t := by
  rw [disjoint_principal_left, ← subset_interior_iff_mem_nhdsSet, interior_compl,
    subset_compl_iff_disjoint_left]

theorem disjoint_nhdsSet_principal : Disjoint (𝓝ˢ s) (𝓟 t) ↔ Disjoint s (closure t) := by
  rw [disjoint_comm, disjoint_principal_nhdsSet, disjoint_comm]

theorem mem_nhdsSet_iff_exists : s ∈ 𝓝ˢ t ↔ ∃ U : Set X, IsOpen U ∧ t ⊆ U ∧ U ⊆ s := by
  rw [← subset_interior_iff_mem_nhdsSet, subset_interior_iff]

theorem eventually_nhdsSet_iff_exists {p : X → Prop} :
    (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∃ t, IsOpen t ∧ s ⊆ t ∧ ∀ x, x ∈ t → p x :=
  mem_nhdsSet_iff_exists

theorem eventually_nhdsSet_iff_forall {p : X → Prop} :
    (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, p y :=
  mem_nhdsSet_iff_forall

theorem hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U => IsOpen U ∧ s ⊆ U) fun U => U :=
  ⟨fun t => by simp [mem_nhdsSet_iff_exists, and_assoc]⟩
