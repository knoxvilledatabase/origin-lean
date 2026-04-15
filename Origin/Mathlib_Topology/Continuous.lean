/-
Extracted from Topology/Continuous.lean
Genuine: 13 of 16 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Continuity in topological spaces

For topological spaces `X` and `Y`, a function `f : X → Y` and a point `x : X`,
`ContinuousAt f x` means `f` is continuous at `x`, and global continuity is
`Continuous f`. There is also a version of continuity `PContinuous` for
partially defined functions.

## Tags

continuity, continuous function
-/

open Set Filter Topology

variable {X Y Z : Type*}

open TopologicalSpace

theorem continuous_def {_ : TopologicalSpace X} {_ : TopologicalSpace Y} {f : X → Y} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  ⟨fun hf => hf.1, fun h => ⟨h⟩⟩

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable {f : X → Y} {s : Set X} {x : X} {y : Y}

theorem IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : IsOpen t) :
    IsOpen (f ⁻¹' t) :=
  hf.isOpen_preimage t h

lemma Equiv.continuous_symm_iff (e : X ≃ Y) : Continuous e.symm ↔ IsOpenMap e := by
  simp_rw [continuous_def, ← Equiv.image_eq_preimage_symm, IsOpenMap]

lemma Equiv.isOpenMap_symm_iff (e : X ≃ Y) : IsOpenMap e.symm ↔ Continuous e := by
  simp_rw [← Equiv.continuous_symm_iff, Equiv.symm_symm]

theorem continuous_congr {g : X → Y} (h : ∀ x, f x = g x) :
    Continuous f ↔ Continuous g :=
  .of_eq <| congrArg _ <| funext h

theorem Continuous.congr {g : X → Y} (h : Continuous f) (h' : ∀ x, f x = g x) : Continuous g :=
  continuous_congr h' |>.mp h

theorem continuousAt_congr {g : X → Y} (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt f x ↔ ContinuousAt g x := by
  simp only [ContinuousAt, tendsto_congr' h, h.eq_of_nhds]

theorem ContinuousAt.congr {g : X → Y} (hf : ContinuousAt f x) (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt g x :=
  (continuousAt_congr h).1 hf

theorem ContinuousAt.eventually_mem {f : X → Y} {x : X} (hf : ContinuousAt f x) {s : Set Y}
    (hs : s ∈ 𝓝 (f x)) : ∀ᶠ y in 𝓝 x, f y ∈ s :=
  hf hs

lemma not_continuousAt_of_tendsto {f : X → Y} {l₁ : Filter X} {l₂ : Filter Y} {x : X}
    (hf : Tendsto f l₁ l₂) [l₁.NeBot] (hl₁ : l₁ ≤ 𝓝 x) (hl₂ : Disjoint (𝓝 (f x)) l₂) :
    ¬ ContinuousAt f x := fun cont ↦
  (cont.mono_left hl₁).not_tendsto hl₂ hf

theorem ClusterPt.map {lx : Filter X} {ly : Filter Y} (H : ClusterPt x lx)
    (hfc : ContinuousAt f x) (hf : Tendsto f lx ly) : ClusterPt (f x) ly :=
  (NeBot.map H f).mono <| hfc.tendsto.inf hf

theorem preimage_interior_subset_interior_preimage {t : Set Y} (hf : Continuous f) :
    f ⁻¹' interior t ⊆ interior (f ⁻¹' t) :=
  interior_maximal (preimage_mono interior_subset) (isOpen_interior.preimage hf)

theorem continuous_iff_preimage_interior_subset_interior_preimage :
    Continuous f ↔ ∀ s, f ⁻¹' (interior s) ⊆ interior (f ⁻¹' s) where
  mp h s := preimage_interior_subset_interior_preimage h
  mpr h := ⟨fun s hs ↦ subset_interior_iff_isOpen.mp <| by grw [← h, hs.interior_eq]⟩
