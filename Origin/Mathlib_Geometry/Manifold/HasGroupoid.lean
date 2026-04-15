/-
Extracted from Geometry/Manifold/HasGroupoid.lean
Genuine: 17 of 20 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Charted spaces with a given structure groupoid
-/

noncomputable section

open TopologicalSpace Topology

universe u

variable {H : Type u} {H' : Type*} {M : Type*} {M' : Type*} {M'' : Type*}

open Set OpenPartialHomeomorph Manifold

section HasGroupoid

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

class HasGroupoid {H : Type*} [TopologicalSpace H] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (G : StructureGroupoid H) : Prop where
  compatible :
    ∀ {e e' : OpenPartialHomeomorph M H}, e ∈ atlas H M → e' ∈ atlas H M → e.symm ≫ₕ e' ∈ G

theorem StructureGroupoid.compatible {H : Type*} [TopologicalSpace H] (G : StructureGroupoid H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G]
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M) :
    e.symm ≫ₕ e' ∈ G :=
  HasGroupoid.compatible he he'

theorem hasGroupoid_of_le {G₁ G₂ : StructureGroupoid H} (h : HasGroupoid M G₁) (hle : G₁ ≤ G₂) :
    HasGroupoid M G₂ :=
  ⟨fun he he' ↦ hle (h.compatible he he')⟩

theorem hasGroupoid_inf_iff {G₁ G₂ : StructureGroupoid H} : HasGroupoid M (G₁ ⊓ G₂) ↔
    HasGroupoid M G₁ ∧ HasGroupoid M G₂ :=
  ⟨(fun h ↦ ⟨hasGroupoid_of_le h inf_le_left, hasGroupoid_of_le h inf_le_right⟩),
  fun ⟨h1, h2⟩ ↦ { compatible := fun he he' ↦ ⟨h1.compatible he he', h2.compatible he he'⟩ }⟩

theorem hasGroupoid_of_pregroupoid (PG : Pregroupoid H) (h : ∀ {e e' : OpenPartialHomeomorph M H},
    e ∈ atlas H M → e' ∈ atlas H M → PG.property (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
    HasGroupoid M PG.groupoid :=
  ⟨fun he he' ↦ mem_groupoid_of_pregroupoid.mpr ⟨h he he', h he' he⟩⟩

-- INSTANCE (free from Core): hasGroupoid_model_space

-- INSTANCE (free from Core): hasGroupoid_continuousGroupoid

theorem StructureGroupoid.trans_restricted {e e' : OpenPartialHomeomorph M H}
    {G : StructureGroupoid H} (he : e ∈ atlas H M) (he' : e' ∈ atlas H M)
    [HasGroupoid M G] [ClosedUnderRestriction G] {s : Opens M} (hs : Nonempty s) :
    (e.subtypeRestr hs).symm ≫ₕ e'.subtypeRestr hs ∈ G :=
  G.mem_of_eqOnSource (closedUnderRestriction' (G.compatible he he')
    (e.isOpen_inter_preimage_symm s.2)) (e.subtypeRestr_symm_trans_subtypeRestr hs e')

section MaximalAtlas

variable (G : StructureGroupoid H)

variable (M) in

def StructureGroupoid.maximalAtlas : Set (OpenPartialHomeomorph M H) :=
  { e | ∀ e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G }

theorem StructureGroupoid.subset_maximalAtlas [HasGroupoid M G] : atlas H M ⊆ G.maximalAtlas M :=
  fun _ he _ he' ↦ ⟨G.compatible he he', G.compatible he' he⟩

theorem StructureGroupoid.chart_mem_maximalAtlas [HasGroupoid M G] (x : M) :
    chartAt H x ∈ G.maximalAtlas M :=
  G.subset_maximalAtlas (chart_mem_atlas H x)

variable {G}

theorem StructureGroupoid.compatible_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ G.maximalAtlas M) (he' : e' ∈ G.maximalAtlas M) : e.symm ≫ₕ e' ∈ G := by
  refine G.locality fun x hx ↦ ?_
  set f := chartAt (H := H) (e.symm x)
  let s := e.target ∩ e.symm ⁻¹' f.source
  have hs : IsOpen s := by
    apply e.symm.continuousOn_toFun.isOpen_inter_preimage <;> apply open_source
  have xs : x ∈ s := by
    simp only [s, f, mem_inter_iff, mem_preimage, mem_chart_source, and_true]
    exact ((mem_inter_iff _ _ _).1 hx).1
  refine ⟨s, hs, xs, ?_⟩
  have A : e.symm ≫ₕ f ∈ G := (mem_maximalAtlas_iff.1 he f (chart_mem_atlas _ _)).1
  have B : f.symm ≫ₕ e' ∈ G := (mem_maximalAtlas_iff.1 he' f (chart_mem_atlas _ _)).2
  have C : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ∈ G := G.trans A B
  have D : (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' ≈ (e.symm ≫ₕ e').restr s := calc
    (e.symm ≫ₕ f) ≫ₕ f.symm ≫ₕ e' = e.symm ≫ₕ (f ≫ₕ f.symm) ≫ₕ e' := by simp only [trans_assoc]
    _ ≈ e.symm ≫ₕ ofSet f.source f.open_source ≫ₕ e' :=
      EqOnSource.trans' (refl _) (EqOnSource.trans' (self_trans_symm _) (refl _))
    _ ≈ (e.symm ≫ₕ ofSet f.source f.open_source) ≫ₕ e' := by rw [trans_assoc]
    _ ≈ e.symm.restr s ≫ₕ e' := by rw [trans_of_set']; apply refl
    _ ≈ (e.symm ≫ₕ e').restr s := by rw [restr_trans]
  exact G.mem_of_eqOnSource C (Setoid.symm D)

open OpenPartialHomeomorph in

lemma StructureGroupoid.mem_maximalAtlas_of_eqOnSource {e e' : OpenPartialHomeomorph M H}
    (h : e' ≈ e) (he : e ∈ G.maximalAtlas M) : e' ∈ G.maximalAtlas M := by
  intro e'' he''
  obtain ⟨l, r⟩ := mem_maximalAtlas_iff.mp he e'' he''
  exact ⟨G.mem_of_eqOnSource l (EqOnSource.trans' (EqOnSource.symm' h) (e''.eqOnSource_refl)),
         G.mem_of_eqOnSource r (EqOnSource.trans' (e''.symm).eqOnSource_refl h)⟩

variable (G)

theorem StructureGroupoid.id_mem_maximalAtlas : OpenPartialHomeomorph.refl H ∈ G.maximalAtlas H :=
  G.subset_maximalAtlas <| by simp

theorem StructureGroupoid.mem_maximalAtlas_of_mem_groupoid {f : OpenPartialHomeomorph H H}
    (hf : f ∈ G) : f ∈ G.maximalAtlas H := by
  rintro e (rfl : e = OpenPartialHomeomorph.refl H)
  exact ⟨G.trans (G.symm hf) G.id_mem, G.trans (G.symm G.id_mem) hf⟩

theorem StructureGroupoid.maximalAtlas_mono {G G' : StructureGroupoid H} (h : G ≤ G') :
    G.maximalAtlas M ⊆ G'.maximalAtlas M :=
  fun _ he e' he' ↦ ⟨h (he e' he').1, h (he e' he').2⟩

private theorem restr_mem_maximalAtlas_aux1 [ClosedUnderRestriction G]
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ G.maximalAtlas M) (he' : e' ∈ atlas H M)
    {s : Set M} (hs : IsOpen s) :
    (e.restr s).symm ≫ₕ e' ∈ G := by
  have hs'' : IsOpen (e '' (e.source ∩ s)) := by
    rw [isOpen_image_iff_of_subset_source _ inter_subset_left]
    exact e.open_source.inter hs
  have : (e.restr (e.source ∩ s)).symm ≫ₕ e' ∈ G := by
    apply G.mem_of_eqOnSource (closedUnderRestriction' (he e' he').1 hs'')
    exact e.restr_symm_trans (e.open_source.inter hs) hs'' inter_subset_left
  refine G.mem_of_eqOnSource this ?_
  exact EqOnSource.trans' (Setoid.symm e.restr_inter_source).symm' (eqOnSource_refl e')

private theorem restr_mem_maximalAtlas_aux2 [ClosedUnderRestriction G]
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ G.maximalAtlas M) (he' : e' ∈ atlas H M)
    {s : Set M} (hs : IsOpen s) :
    e'.symm ≫ₕ e.restr s ∈ G := by
  have hs'' : IsOpen (e' '' (e'.source ∩ s)) := by
    rw [isOpen_image_iff_of_subset_source e' inter_subset_left]
    exact e'.open_source.inter hs
  have ht : IsOpen (e'.target ∩ e'.symm ⁻¹' s) := by
    rw [← image_source_inter_eq']
    exact isOpen_image_source_inter e' hs
  exact G.mem_of_eqOnSource (closedUnderRestriction' (he e' he').2 ht) (e.symm_trans_restr e' hs)

theorem restr_mem_maximalAtlas [ClosedUnderRestriction G]
    {e : OpenPartialHomeomorph M H} (he : e ∈ G.maximalAtlas M) {s : Set M} (hs : IsOpen s) :
    e.restr s ∈ G.maximalAtlas M :=
  fun _e' he' ↦ ⟨restr_mem_maximalAtlas_aux1 G he he' hs, restr_mem_maximalAtlas_aux2 G he he' hs⟩

end MaximalAtlas

section Singleton

variable {α : Type*} [TopologicalSpace α]

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph α H)
