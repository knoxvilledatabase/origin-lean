/-
Extracted from Topology/Semicontinuity/Hemicontinuity.lean
Genuine: 15 of 15 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Hemicontinuity

This files provides basic facts about upper and lower hemicontinuity of correspondences
`f : α → Set β`.
-/

open Set Filter Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

variable {f g : α → Set β} {s : Set α} {x : α}

/-! ### Basic facts -/

lemma upperHemicontinuousWithinAt_iff_forall_isOpen :
    UpperHemicontinuousWithinAt f s x ↔ ∀ u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝[s] x, f x' ⊆ u := by
  rw [upperHemicontinuousWithinAt_iff, hasBasis_nhdsSet _ |>.forall_iff ?mono]
  case mono => exact fun t₁ t₂ ht h ↦ h.mp <| .of_forall fun x' ↦ by gcongr
  simp only [and_imp]
  apply forall₂_congr
  simp +contextual [← subset_interior_iff_mem_nhdsSet, IsOpen.interior_eq]

alias ⟨UpperHemicontinuousWithinAt.forall_isOpen, UpperHemicontinuousWithinAt.of_forall_isOpen⟩ :=

  upperHemicontinuousWithinAt_iff_forall_isOpen

lemma upperHemicontinuousOn_iff_forall_isOpen :
    UpperHemicontinuousOn f s ↔ ∀ x ∈ s, ∀ u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝[s] x, f x' ⊆ u := by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuousOn.forall_isOpen, UpperHemicontinuousOn.of_forall_isOpen⟩ :=

  upperHemicontinuousOn_iff_forall_isOpen

lemma upperHemicontinuousAt_iff_forall_isOpen :
    UpperHemicontinuousAt f x ↔ ∀ u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝 x, f x' ⊆ u := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_forall_isOpen (s := Set.univ)

alias ⟨UpperHemicontinuousAt.forall_isOpen, UpperHemicontinuousAt.of_forall_isOpen⟩ :=

  upperHemicontinuousAt_iff_forall_isOpen

lemma upperHemicontinuous_iff_forall_isOpen :
    UpperHemicontinuous f ↔ ∀ x u, IsOpen u → f x ⊆ u → ∀ᶠ x' in 𝓝 x, f x' ⊆ u := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_forall_isOpen]

alias ⟨UpperHemicontinuous.forall_isOpen, UpperHemicontinuous.of_forall_isOpen⟩ :=

  upperHemicontinuous_iff_forall_isOpen

/-! ### Characterization in terms of preimages of intervals of sets -/

lemma upperHemicontinuousWithinAt_iff_preimage_Iic :
    UpperHemicontinuousWithinAt f s x ↔ ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝[s] x := by
  simp_rw [upperHemicontinuousWithinAt_iff]
  rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₁, hasBasis_nhdsSet (f x) |>.forall_iff ?h₂]
  case h₂ =>
    intro s t hst
    gcongr
    exact hst
  case h₁ =>
    intro s t hst
    gcongr
  refine forall₂_congr fun u ⟨hu, hfu⟩ ↦ ?_
  simp [hu.mem_nhdsSet, eventually_iff, Iic]

lemma upperHemicontinuousAt_iff_preimage_Iic :
    UpperHemicontinuousAt f x ↔ ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝 x := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_preimage_Iic (s := univ)

lemma upperHemicontinuousOn_iff_preimage_Iic :
    UpperHemicontinuousOn f s ↔ ∀ x ∈ s, ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝[s] x := by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_preimage_Iic]

lemma upperHemicontinuous_iff_preimage_Iic :
    UpperHemicontinuous f ↔ ∀ x, ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝 x := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_preimage_Iic]

lemma upperHemicontinuous_iff_isOpen_preimage_Iic :
    UpperHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen (f ⁻¹' (Iic u)) := by
  simp_rw [upperHemicontinuous_iff_preimage_Iic, isOpen_iff_mem_nhds (s := f ⁻¹' (Iic _))]
  conv =>
    enter [1, x]
    rw [hasBasis_nhdsSet (f x) |>.forall_iff <|
      fun s t hst ↦ by gcongr; exact hst]
  simp [forall_comm (α := α)]

lemma upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl :
    UpperHemicontinuous f ↔ ∀ u, IsClosed u → IsClosed (f ⁻¹' (Iic uᶜ))ᶜ := by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact upperHemicontinuous_iff_isOpen_preimage_Iic

lemma isClosedMap_iff_upperHemicontinuous {f : α → β} :
    IsClosedMap f ↔ UpperHemicontinuous (f ⁻¹' {·}) := by
  rw [isClosedMap_iff_kernImage, upperHemicontinuous_iff_isOpen_preimage_Iic]
  aesop

lemma lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl :
    LowerHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen (f ⁻¹' (Iic uᶜ))ᶜ := by
  have (u : Set β) : (f ⁻¹' (Iic uᶜ))ᶜ = {x | (f x ∩ u).Nonempty} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff, this, isOpen_iff_mem_nhds,
    forall_comm (α := α), mem_setOf, Filter.Eventually]

lemma lowerHemicontinuous_iff_isClosed_preimage_Iic :
    LowerHemicontinuous f ↔ ∀ u, IsClosed u → IsClosed (f ⁻¹' (Iic u)) := by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl

lemma isOpenMap_iff_lowerHemicontinuous {f : α → β} :
    IsOpenMap f ↔ LowerHemicontinuous (f ⁻¹' {·}) := by
  rw [isOpenMap_iff_kernImage, lowerHemicontinuous_iff_isClosed_preimage_Iic]
  aesop

/-! ### Singleton maps -/

lemma upperHemicontinuous_singleton_id : UpperHemicontinuous ({·} : α → Set α) := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff]
