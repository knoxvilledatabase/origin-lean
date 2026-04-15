/-
Extracted from RingTheory/Lasker.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Lasker ring

## Main declarations

- `IsLasker`: An `R`-module `M` satisfies `IsLasker R M` when any `N : Submodule R M` can be
  decomposed into finitely many primary submodules.
- `IsLasker.exists_isMinimalPrimaryDecomposition`: Any `N : Submodule R N` in an `R`-module `M`
  satisfying `IsLasker R M` can be decomposed into finitely many primary submodules `Nᵢ`, such
  that the decomposition is minimal: each `Nᵢ` is necessary, and the `√Ann(M/Nᵢ)` are distinct.
- `IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes`: The first uniqueness theorem
  for primary decomposition, Theorem 4.5 in Atiyah-Macdonald: In any minimal primary decomposition
  `I = ⨅ i, q_i`, the ideals `radical (q_i.colon M)` are exactly the associated primes of `I`.
- `Submodule.isLasker`: Every Noetherian module is Lasker.

-/

section IsLasker

open Ideal

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

def IsLasker : Prop :=
  ∀ N : Submodule R M, ∃ s : Finset (Submodule R M), s.inf id = N ∧ ∀ ⦃J⦄, J ∈ s → J.IsPrimary

variable {R M}

namespace Submodule

lemma decomposition_erase_inf {N : Submodule R M}
    {s : Finset (Submodule R M)} (hs : s.inf id = N) :
    ∃ t : Finset (Submodule R M), t ⊆ s ∧ t.inf id = N ∧
      ∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J := by
  induction s using Finset.eraseInduction with
  | H s IH =>
    by_cases! H : ∀ J ∈ s, ¬ (s.erase J).inf id ≤ J
    · exact ⟨s, Finset.Subset.rfl, hs, H⟩
    obtain ⟨J, hJ, hJ'⟩ := H
    refine (IH _ hJ ?_).imp
      fun t ↦ And.imp_left (fun ht ↦ ht.trans (Finset.erase_subset _ _))
    rw [← Finset.insert_erase hJ] at hs
    simp [← hs, hJ']

open scoped Function -- required for scoped `on` notation

lemma isPrimary_decomposition_pairwise_ne_radical {N : Submodule R M}
    {s : Finset (Submodule R M)} (hs : s.inf id = N) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Submodule R M), t.inf id = N ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      (t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical) := by
  classical
  refine ⟨(s.image fun J ↦ {I ∈ s | (I.colon .univ).radical = (J.colon .univ).radical}).image
    fun t ↦ t.inf id, ?_, ?_, ?_⟩
  · ext
    grind [Finset.inf_image, Submodule.mem_finsetInf]
  · simp only [Finset.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
    intro J hJ
    refine isPrimary_finsetInf (i := J) ?_ ?_ (by simp)
    · simp [hJ]
    · simp only [Finset.mem_filter, id_eq, and_imp]
      intro y hy
      simp [hs' hy]
  · intro I hI J hJ hIJ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, exists_exists_and_eq_and] at hI hJ
    obtain ⟨I', hI', hI⟩ := hI
    obtain ⟨J', hJ', hJ⟩ := hJ
    simp only [Function.onFun, ne_eq]
    contrapose hIJ
    suffices (I'.colon Set.univ).radical = (J'.colon Set.univ).radical by
      rw [← hI, ← hJ, this]
    · rw [← hI, colon_finsetInf,
        radical_finset_inf (i := I') (by simp [hI']) (by simp), id_eq] at hIJ
      rw [hIJ, ← hJ, colon_finsetInf,
        radical_finset_inf (i := J') (by simp [hJ']) (by simp), id_eq]

lemma exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition
    {N : Submodule R M} {s : Finset (Submodule R M)}
    (hs : s.inf id = N) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Submodule R M), t.inf id = N ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      ((t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical)) ∧
      (∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J) := by
  obtain ⟨t, ht, ht', ht''⟩ := isPrimary_decomposition_pairwise_ne_radical hs hs'
  obtain ⟨u, hut, hu, hu'⟩ := decomposition_erase_inf ht
  exact ⟨u, hu, fun _ hi ↦ ht' (hut hi), ht''.mono hut, hu'⟩

structure IsMinimalPrimaryDecomposition
    (N : Submodule R M) (t : Finset (Submodule R M)) where
  inf_eq : t.inf id = N
  primary : ∀ ⦃J⦄, J ∈ t → J.IsPrimary
  distinct : (t : Set (Submodule R M)).Pairwise ((· ≠ ·) on fun J ↦ (J.colon Set.univ).radical)
  minimal : ∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J

namespace IsMinimalPrimaryDecomposition

lemma injOn (N : Submodule R M)
    (t : Finset (Submodule R M)) (ht : N.IsMinimalPrimaryDecomposition t) :
    Set.InjOn (fun J ↦ (J.colon Set.univ).radical) (t : Set (Submodule R M)) :=
  Set.injOn_iff_pairwise_ne.mpr ht.distinct

lemma image_radical_eq_associated_primes
    {N : Submodule R M} {t : Finset (Submodule R M)} (ht : IsMinimalPrimaryDecomposition N t) :
    (fun J : Submodule R M ↦ (J.colon Set.univ).radical) '' t = N.associatedPrimes := by
  classical
  replace h x : radical (N.colon {x}) = (t.filter (x ∉ ·)).inf fun q ↦ radical (q.colon .univ) := by
    simp_rw [← ht.inf_eq, colon_finsetInf, ← radicalInfTopHom_apply, map_finset_inf,
      Function.comp_def, radicalInfTopHom_apply, id_eq]
    rw [Finset.inf_congr rfl (fun q hq ↦ (ht.primary hq).radical_colon_singleton_eq_ite x),
      Finset.inf_ite, Finset.inf_top, top_inf_eq]
  ext p
  constructor
  · rintro ⟨q, hqt, rfl⟩
    obtain ⟨x, hxt, hxq⟩ := SetLike.not_le_iff_exists.mp (ht.minimal hqt)
    use (ht.primary hqt).isPrime_radical_colon, x
    rw [h, ← Finset.insert_erase (Finset.mem_filter.mpr ⟨hqt, hxq⟩), Finset.inf_insert,
      eq_comm, inf_eq_left, Finset.le_inf_iff]
    simp only [mem_finsetInf, Finset.mem_erase] at hxt
    grind
  · rintro ⟨hp, x, rfl⟩
    rw [h] at hp ⊢
    obtain ⟨q, hq1, hq2⟩ := eq_inf_of_isPrime_inf hp
    exact ⟨q, Finset.mem_of_mem_filter q hq1, hq2⟩
