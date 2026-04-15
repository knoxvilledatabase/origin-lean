/-
Extracted from RingTheory/IsPrimary.lean
Genuine: 6 of 9 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!
# Primary submodules

A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.

## Main results

* `Submodule.isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul`:
  A `N : Submodule R M` is primary if any zero divisor on `M ⧸ N` is nilpotent.
  See https://mathoverflow.net/questions/3910/primary-decomposition-for-modules
  for a comparison of this definition (a la Atiyah-Macdonald) vs "locally nilpotent" (Matsumura).

## Implementation details

This is a generalization of `Ideal.IsPrimary`. For brevity, the pointwise instances are used
to define the nilpotency of `r : R`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
  Chapter 4, Exercise 21.

-/

open Pointwise

namespace Submodule

open Ideal

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

protected def IsPrimary (S : Submodule R M) : Prop :=
  S ≠ ⊤ ∧ ∀ {r : R} {x : M}, r • x ∈ S → x ∈ S ∨ ∃ n : ℕ, (r ^ n • ⊤ : Submodule R M) ≤ S

variable {S T : Submodule R M}

protected lemma IsPrimary.inf (hS : S.IsPrimary) (hT : T.IsPrimary)
    (h : (S.colon Set.univ).radical = (T.colon Set.univ).radical) :
    (S ⊓ T).IsPrimary := by
  obtain ⟨_, hS⟩ := hS
  obtain ⟨_, hT⟩ := hT
  refine ⟨by grind, fun ⟨hS', hT'⟩ ↦ ?_⟩
  simp_rw [← mem_colon_iff_le, ← Ideal.mem_radical_iff, inf_colon, Ideal.radical_inf,
    top_coe, h, inf_idem, mem_inf, and_or_right] at hS hT ⊢
  exact ⟨hS hS', hT hT'⟩

open Finset in

lemma isPrimary_finsetInf {ι : Type*} {s : Finset ι} {f : ι → Submodule R M} {i : ι} (hi : i ∈ s)
    (hs : ∀ ⦃y⦄, y ∈ s → (f y).IsPrimary)
    (hs' : ∀ ⦃y⦄, y ∈ s → ((f y).colon Set.univ).radical = ((f i).colon Set.univ).radical) :
    (s.inf f).IsPrimary := by
  classical
  induction s using Finset.induction_on generalizing i with
  | empty => simp at hi
  | insert a s ha IH =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp only [insert_empty_eq, mem_singleton] at hi
      simpa [hi] using hs
    simp only [inf_insert]
    have H ⦃x⦄ (hx : x ∈ s) : ((f x).colon Set.univ).radical = ((f y).colon Set.univ).radical := by
      rw [hs' (mem_insert_of_mem hx), hs' (mem_insert_of_mem hy)]
    refine IsPrimary.inf (hs (by simp)) (IH hy (fun x hx ↦ hs (by simp [hx])) H) ?_
    rw [colon_finsetInf, Ideal.radical_finset_inf hy H,
      hs' (mem_insert_self _ _), hs' (mem_insert_of_mem hy)]

theorem IsPrimary.isPrime_radical_colon (hI : S.IsPrimary) : (S.colon .univ).radical.IsPrime := by
  refine isPrime_iff.mpr <| hI.imp (by simp) fun h x y ⟨n, hn⟩ ↦ ?_
  simp_rw [← mem_colon_iff_le, ← mem_radical_iff] at h
  refine or_iff_not_imp_left.mpr fun hx ↦ ⟨n, ?_⟩
  simp only [mul_pow, mem_colon, Set.mem_univ, true_imp_iff, mul_smul] at hn ⊢
  exact fun p ↦ (h (hn p)).resolve_right (mt mem_radical_of_pow_mem hx)

theorem IsPrimary.radical_colon_singleton_of_notMem (hI : S.IsPrimary) {m : M} (hm : m ∉ S) :
    (S.colon {m}).radical = (S.colon Set.univ).radical :=
  le_antisymm (radical_le_radical_iff.mpr fun _ hy ↦
    (hI.2 (Submodule.mem_colon_singleton.mp hy)).resolve_left hm)
    (radical_mono (Submodule.colon_mono le_rfl (Set.subset_univ {m})))

theorem IsPrimary.radical_colon_singleton_eq_ite (hS : S.IsPrimary) (m : M) [Decidable (m ∈ S)] :
    radical (S.colon {m}) = if m ∈ S then ⊤ else radical (S.colon Set.univ) := by
  split_ifs with hm
  · rwa [radical_eq_top, colon_eq_top_iff_subset, Set.singleton_subset_iff]
  · exact hS.radical_colon_singleton_of_notMem hm

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {S : Submodule R M}

-- DISSOLVED: isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul

end CommRing

end Submodule
