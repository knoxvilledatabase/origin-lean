/-
Extracted from Combinatorics/Matroid/Sum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sums of matroids

The *sum* `M` of a collection `M₁, M₂, ..` of matroids is a matroid on the disjoint union of
the ground sets of the summands, in which the independent sets are precisely the unions of
independent sets of the summands.

We can ask for such a sum both for pairs and for arbitrary indexed collections of matroids,
and we can also ask for the 'disjoint union' to be either set-theoretic or type-theoretic.
To this end, we define five separate versions of the sum construction.

## Main definitions

* For an indexed collection `M : (i : ι) → Matroid (α i)` of matroids on different types,
  `Matroid.sigma M` is the sum of the `M i`, as a matroid on the sigma type `(Σ i, α i)`.

* For an indexed collection `M : ι → Matroid α` of matroids on the same type,
  `Matroid.sum' M` is the sum of the `M i`, as a matroid on the product type `ι × α`.

* For an indexed collection `M : ι → Matroid α` of matroids on the same type, and a
  proof `h : Pairwise (Disjoint on fun i ↦ (M i).E)` that they have disjoint ground sets,
  `Matroid.disjointSigma M h` is the sum of the `M` as a `Matroid α` with ground set `⋃ i, (M i).E`.

* `Matroid.sum (M : Matroid α) (N : Matroid β)` is the sum of `M` and `N` as a matroid on `α ⊕ β`.

* If `M N : Matroid α` and `h : Disjoint M.E N.E`, then `Matroid.disjointSum M N h` is the sum
  of `M` and `N` as a `Matroid α` with ground set `M.E ∪ N.E`.

## Implementation details

We only directly define a matroid for `Matroid.sigma`. All other versions of sum are
defined indirectly, using `Matroid.sigma` and the API in `Matroid.map`.
-/

assert_not_exists Field

universe u v

open Set

namespace Matroid

section Sigma

variable {ι : Type*} {α : ι → Type*} {M : (i : ι) → Matroid (α i)}

protected def sigma (M : (i : ι) → Matroid (α i)) : Matroid ((i : ι) × α i) where
  E := univ.sigma (fun i ↦ (M i).E)
  Indep I := ∀ i, (M i).Indep (Sigma.mk i ⁻¹' I)
  IsBase B := ∀ i, (M i).IsBase (Sigma.mk i ⁻¹' B)

  indep_iff' I := by
    refine ⟨fun h ↦ ?_, fun ⟨B, hB, hIB⟩ i ↦ (hB i).indep.subset (preimage_mono hIB)⟩
    choose Bs hBs using fun i ↦ (h i).exists_isBase_superset
    refine ⟨univ.sigma Bs, fun i ↦ by simpa using (hBs i).1, ?_⟩
    rw [← univ_sigma_preimage_mk I]
    refine sigma_mono rfl.subset fun i ↦ (hBs i).2

  exists_isBase := by
    choose B hB using fun i ↦ (M i).exists_isBase
    exact ⟨univ.sigma B, by simpa⟩

  isBase_exchange B₁ B₂ h₁ h₂ := by
    simp only [mem_diff, Sigma.exists, and_imp, Sigma.forall]
    intro i e he₁ he₂
    have hf_ex := (h₁ i).exchange (h₂ i) ⟨he₁, by simpa⟩
    obtain ⟨f, ⟨hf₁, hf₂⟩, hfB⟩ := hf_ex
    refine ⟨i, f, ⟨hf₁, hf₂⟩, fun j ↦ ?_⟩
    rw [← union_singleton, preimage_union, preimage_diff]
    obtain (rfl | hne) := eq_or_ne i j
    · simpa only [show ∀ x, {⟨i,x⟩} = Sigma.mk i '' {x} by simp,
        preimage_image_eq _ sigma_mk_injective, union_singleton]
    rw [preimage_singleton_eq_empty.2 (by simpa), preimage_singleton_eq_empty.2 (by simpa),
      diff_empty, union_empty]
    exact h₁ j

  maximality X _ I hI hIX := by
    choose Js hJs using
      fun i ↦ (hI i).subset_isBasis'_of_subset (preimage_mono (f := Sigma.mk i) hIX)
    use univ.sigma Js
    simp only [maximal_subset_iff', mem_univ, mk_preimage_sigma, and_imp]
    refine ⟨?_, ⟨fun i ↦ (hJs i).1.indep, ?_⟩, fun S hS hSX hJS ↦ ?_⟩
    · rw [← univ_sigma_preimage_mk I]
      exact sigma_mono rfl.subset fun i ↦ (hJs i).2
    · rw [← univ_sigma_preimage_mk X]
      exact sigma_mono rfl.subset fun i ↦ (hJs i).1.subset
    rw [← univ_sigma_preimage_mk S]
    refine sigma_mono rfl.subset fun i ↦ ?_
    rw [sigma_subset_iff] at hJS
    rw [(hJs i).1.eq_of_subset_indep (hS i) (hJS <| mem_univ i)]
    exact preimage_mono hSX

  subset_ground B hB := by
    rw [← univ_sigma_preimage_mk B]
    apply sigma_mono Subset.rfl fun i ↦ (hB i).subset_ground
