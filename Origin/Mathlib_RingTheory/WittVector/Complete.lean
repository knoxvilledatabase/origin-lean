/-
Extracted from RingTheory/WittVector/Complete.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The ring of Witt vectors is p-torsion free and p-adically complete

In this file, we prove that the ring of Witt vectors `𝕎 k` is p-torsion free and p-adically complete
when `k` is a perfect ring of characteristic `p`.

## Main declarations

* `WittVector.eq_zero_of_p_mul_eq_zero` : If `k` is a perfect ring of characteristic `p`,
  then the Witt vector `𝕎 k` is `p`-torsion free.
* `isAdicCompleteIdealSpanP` : If `k` is a perfect ring of characteristic `p`,
  then the Witt vector `𝕎 k` is `p`-adically complete.
-/

namespace WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {k : Type*} [CommRing k]

local notation "𝕎" => WittVector p

theorem le_coeff_eq_iff_le_sub_coeff_eq_zero {x y : 𝕎 k} {n : ℕ} :
    (∀ i < n, x.coeff i = y.coeff i) ↔ ∀ i < n, (x - y).coeff i = 0 := by
  calc
  _ ↔ x.truncate n = y.truncate n := by
    refine ⟨fun h => ?_, fun h i hi => ?_⟩
    · ext i
      simp [h i]
    · rw [← coeff_truncate x ⟨i, hi⟩, ← coeff_truncate y ⟨i, hi⟩, h]
  _ ↔ (x - y).truncate n = 0 := by
    simp only [map_sub, sub_eq_zero]
  _ ↔ _ := by simp only [← mem_ker_truncate, RingHom.mem_ker]

section PerfectRing

variable [CharP k p] [PerfectRing k p]

theorem eq_zero_of_p_mul_eq_zero (x : 𝕎 k) (h : x * p = 0) : x = 0 := by
  rwa [← frobenius_verschiebung, _root_.map_eq_zero_iff _ (frobenius_bijective p k).injective,
      _root_.map_eq_zero_iff _ (verschiebung_injective p k)] at h

theorem mem_span_p_iff_coeff_zero_eq_zero (x : 𝕎 k) :
    x ∈ (Ideal.span {(p : 𝕎 k)}) ↔ x.coeff 0 = 0 := by
  simp_rw [Ideal.mem_span_singleton, dvd_def, mul_comm]
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [hu, mul_charP_coeff_zero]
  · use (frobeniusEquiv p k).symm (x.shift 1)
    calc
    _ = verschiebung (x.shift 1) := by
      simpa using eq_iterate_verschiebung (n := 1) (by simp [h])
    _ = _ := by
      rw [← verschiebung_frobenius, ← frobeniusEquiv_apply,
          RingEquiv.apply_symm_apply (frobeniusEquiv p k) _]

theorem mem_span_p_pow_iff_le_coeff_eq_zero (x : 𝕎 k) (n : ℕ) :
    x ∈ (Ideal.span {(p ^ n : 𝕎 k)}) ↔ ∀ m, m < n → x.coeff m = 0 := by
  simp_rw [Ideal.mem_span_singleton, dvd_def, mul_comm]
  refine ⟨fun ⟨u, hu⟩ m hm ↦ ?_, fun h ↦ ?_⟩
  · rw [hu, mul_pow_charP_coeff_zero _ hm]
  · use (frobeniusEquiv p k).symm^[n] (x.shift n)
    rw [← iterate_verschiebung_iterate_frobenius]
    calc
    _ = verschiebung^[n] (x.shift n) := by
      simpa using eq_iterate_verschiebung (x := x) (n := n) h
    _ = _ := by
      congr
      rw [← Function.comp_apply (f := frobenius^[n]), ← Function.Commute.comp_iterate]
      · rw [← WittVector.frobeniusEquiv_apply, ← RingEquiv.coe_trans]
        simp
      · rw [Function.Commute, Function.Semiconj, ← WittVector.frobeniusEquiv_apply]
        simp only [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply, implies_true]

lemma ker_constantCoeff : RingHom.ker constantCoeff = Ideal.span {(p : 𝕎 k)} := by
  ext
  simp [mem_span_p_iff_coeff_zero_eq_zero]

noncomputable def quotientPEquiv : 𝕎 k ⧸ Ideal.span {(p : 𝕎 k)} ≃+* k :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective (constantCoeff_surjective p))
