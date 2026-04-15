/-
Extracted from Data/Set/Lattice/Image.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The set lattice and (pre)images of functions

This file contains lemmas on the interaction between the indexed union/intersection of sets
and the image and preimage operations: `Set.image`, `Set.preimage`, `Set.image2`, `Set.kernImage`.
It also covers `Set.MapsTo`, `Set.InjOn`, `Set.SurjOn`, `Set.BijOn`.

In order to accommodate `Set.image2`, the file includes results on union/intersection in products.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `iUnion`
* `⋂ i, s i` is called `iInter`
* `⋃ i j, s i j` is called `iUnion₂`. This is an `iUnion` inside an `iUnion`.
* `⋂ i j, s i j` is called `iInter₂`. This is an `iInter` inside an `iInter`.
* `⋃ i ∈ s, t i` is called `biUnion` for "bounded `iUnion`". This is the special case of `iUnion₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `biInter` for "bounded `iInter`". This is the special case of `iInter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `Set.iUnion`
* `⋂`: `Set.iInter`
* `⋃₀`: `Set.sUnion`
* `⋂₀`: `Set.sInter`
-/

open Function Set

universe u

variable {α β γ δ : Type*} {ι ι' ι₂ : Sort*} {κ : ι → Sort*}

namespace Set

section GaloisConnection

variable {f : α → β}

protected theorem image_preimage : GaloisConnection (image f) (preimage f) := fun _ _ =>
  image_subset_iff

protected theorem preimage_kernImage : GaloisConnection (preimage f) (kernImage f) := fun _ _ =>
  subset_kernImage_iff.symm

end GaloisConnection

section kernImage

variable {f : α → β}

lemma kernImage_mono : Monotone (kernImage f) :=
  Set.preimage_kernImage.monotone_u

lemma kernImage_eq_compl {s : Set α} : kernImage f s = (f '' sᶜ)ᶜ :=
  Set.preimage_kernImage.u_unique (Set.image_preimage.compl)
    (fun t ↦ compl_compl (f ⁻¹' t) ▸ Set.preimage_compl)

lemma kernImage_compl {s : Set α} : kernImage f (sᶜ) = (f '' s)ᶜ := by
  rw [kernImage_eq_compl, compl_compl]

lemma kernImage_empty : kernImage f ∅ = (range f)ᶜ := by
  rw [kernImage_eq_compl, compl_empty, image_univ]

lemma kernImage_preimage_eq_iff {s : Set β} : kernImage f (f ⁻¹' s) = s ↔ (range f)ᶜ ⊆ s := by
  rw [kernImage_eq_compl, ← preimage_compl, compl_eq_comm, eq_comm, image_preimage_eq_iff,
      compl_subset_comm]

lemma compl_range_subset_kernImage {s : Set α} : (range f)ᶜ ⊆ kernImage f s := by
  rw [← kernImage_empty]
  exact kernImage_mono (empty_subset _)

lemma kernImage_union_preimage {s : Set α} {t : Set β} :
    kernImage f (s ∪ f ⁻¹' t) = kernImage f s ∪ t := by
  rw [kernImage_eq_compl, kernImage_eq_compl, compl_union, ← preimage_compl, image_inter_preimage,
      compl_inter, compl_compl]

lemma kernImage_preimage_union {s : Set α} {t : Set β} :
    kernImage f (f ⁻¹' t ∪ s) = t ∪ kernImage f s := by
  rw [union_comm, kernImage_union_preimage, union_comm]

end kernImage

theorem image_projection_prod {ι : Type*} {α : ι → Type*} {v : ∀ i : ι, Set (α i)}
    (hv : (pi univ v).Nonempty) (i : ι) :
    ((fun x : ∀ i : ι, α i => x i) '' ⋂ k, (fun x : ∀ j : ι, α j => x k) ⁻¹' v k) = v i := by
  classical
    apply Subset.antisymm
    · simp [iInter_subset]
    · intro y y_in
      simp only [mem_image, mem_iInter, mem_preimage]
      rcases hv with ⟨z, hz⟩
      refine ⟨Function.update z i y, ?_, update_self i y z⟩
      rw [@forall_update_iff ι α _ z i y fun i t => t ∈ v i]
      exact ⟨y_in, fun j _ => by simpa using hz j⟩

/-! ### Bounded unions and intersections -/

section Function

/-! ### Lemmas about `Set.MapsTo` -/
