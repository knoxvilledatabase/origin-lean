/-
Extracted from Topology/UniformSpace/UniformEmbedding.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Uniform embeddings of uniform spaces.

Extension of uniform continuous functions.
-/

open Filter Function Set Uniformity Topology

open scoped SetRel

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {f : α → β}

/-!
### Uniform inducing maps
-/

lemma isUniformInducing_iff_uniformSpace {f : α → β} :
    IsUniformInducing f ↔ ‹UniformSpace β›.comap f = ‹UniformSpace α› := by
  rw [isUniformInducing_iff, UniformSpace.ext_iff, Filter.ext_iff]
  rfl

protected alias ⟨IsUniformInducing.comap_uniformSpace, _⟩ := isUniformInducing_iff_uniformSpace

lemma isUniformInducing_iff' {f : α → β} :
    IsUniformInducing f ↔ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) ≤ 𝓤 α := by
  rw [isUniformInducing_iff, UniformContinuous, tendsto_iff_comap, le_antisymm_iff, and_comm]; rfl

protected lemma Filter.HasBasis.isUniformInducing_iff {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α → β} :
    IsUniformInducing f ↔
      (∀ i, p' i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ s' i) ∧
        (∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j) := by
  simp [isUniformInducing_iff', h.uniformContinuous_iff h', (h'.comap _).le_basis_iff h, subset_def]

theorem IsUniformInducing.mk' {f : α → β}
    (h : ∀ s, s ∈ 𝓤 α ↔ ∃ t ∈ 𝓤 β, ∀ x y : α, (f x, f y) ∈ t → (x, y) ∈ s) : IsUniformInducing f :=
  ⟨by simp [eq_comm, Filter.ext_iff, subset_def, h]⟩

theorem IsUniformInducing.id : IsUniformInducing (@id α) :=
  ⟨by rw [← Prod.map_def, Prod.map_id, comap_id]⟩

theorem IsUniformInducing.comp {g : β → γ} (hg : IsUniformInducing g) {f : α → β}
    (hf : IsUniformInducing f) : IsUniformInducing (g ∘ f) :=
  ⟨by rw [← hf.1, ← hg.1, comap_comap]; rfl⟩

theorem IsUniformInducing.of_comp_iff {g : β → γ} (hg : IsUniformInducing g) {f : α → β} :
    IsUniformInducing (g ∘ f) ↔ IsUniformInducing f := by
  refine ⟨fun h ↦ ?_, hg.comp⟩
  rw [isUniformInducing_iff, ← hg.comap_uniformity, comap_comap, ← h.comap_uniformity,
    Function.comp_def, Function.comp_def]

theorem IsUniformInducing.basis_uniformity {f : α → β} (hf : IsUniformInducing f) {ι : Sort*}
    {p : ι → Prop} {s : ι → Set (β × β)} (H : (𝓤 β).HasBasis p s) :
    (𝓤 α).HasBasis p fun i => Prod.map f f ⁻¹' s i :=
  hf.1 ▸ H.comap _

theorem IsUniformInducing.cauchy_map_iff {f : α → β} (hf : IsUniformInducing f) {F : Filter α} :
    Cauchy (map f F) ↔ Cauchy F := by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap, ← hf.comap_uniformity]

theorem IsUniformInducing.of_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) (hgf : IsUniformInducing (g ∘ f)) : IsUniformInducing f := by
  refine ⟨le_antisymm ?_ hf.le_comap⟩
  rw [← hgf.1, ← Prod.map_def, ← Prod.map_def, ← Prod.map_comp_map f f g g, ← comap_comap]
  exact comap_mono hg.le_comap

theorem IsUniformInducing.uniformContinuous {f : α → β} (hf : IsUniformInducing f) :
    UniformContinuous f := (isUniformInducing_iff'.1 hf).1

theorem IsUniformInducing.uniformContinuous_iff {f : α → β} {g : β → γ} (hg : IsUniformInducing g) :
    UniformContinuous f ↔ UniformContinuous (g ∘ f) := by
  dsimp only [UniformContinuous, Tendsto]
  simp only [← hg.comap_uniformity, ← map_le_iff_le_comap, Filter.map_map, Function.comp_def]
