/-
Extracted from LinearAlgebra/AffineSpace/Ceva.lean
Genuine: 2 of 5 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!
# Ceva's theorem.

This file proves various versions of Ceva's theorem.

## References

* https://en.wikipedia.org/wiki/Ceva%27s_theorem

-/

open scoped Affine

variable {k V P ι : Type*}

namespace AffineIndependent

variable [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

private lemma exists_affineCombination_eq_smul_eq_aux {p : ι → P} (hp : AffineIndependent k p)
    {s : Set ι} (hs : s.Nonempty) {fs : s → Finset ι} (hfs : ∀ i, (i : ι) ∈ fs i) {w : s → ι → k}
    (hw : ∀ i, ∑ j ∈ fs i, w i j = 1) {p' : P}
    (hp' : ∀ i : s, p' ∈ line[k, p i, (fs i).affineCombination k p (w i)]) :
    ∃ (w' : ι → k) (fs' : Finset ι), (∑ j ∈ fs', w' j = 1) ∧ fs'.affineCombination k p w' = p' ∧
      ∀ i : s, ∃ r, ∀ j, r * Set.indicator ((fs i : Set ι) \ {(i : ι)}) (w i) j =
        Set.indicator ((fs' : Set ι) \ {(i : ι)}) w' j := by
  classical
  have hp'' : ∀ i : s, ∃ r : k, (fs i).affineCombination k p
      (AffineMap.lineMap (Finset.affineCombinationSingleWeights k (i : ι)) (w i) r) = p' := by
    intro i
    simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp'
    obtain ⟨r, rfl⟩ := hp' i
    exact ⟨r, by simp [hfs]⟩
  obtain ⟨i', hi'⟩ := hs
  obtain ⟨ri', hri'⟩ := hp'' ⟨i', hi'⟩
  let w' : ι → k :=
    AffineMap.lineMap (Finset.affineCombinationSingleWeights k i') (w ⟨i', hi'⟩) ri'
  refine ⟨w', fs ⟨i', hi'⟩, ?_, ?_, ?_⟩
  · simp [w', AffineMap.lineMap_apply_module, Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]
  · simp [w', hri']
  · intro i
    obtain ⟨r, hr⟩ := hp'' i
    refine ⟨r, ?_⟩
    rw [← hri'] at hr
    simp only [AffineMap.lineMap_apply_module] at hr
    have hind := hp.indicator_eq_of_affineCombination_eq _ _ _ _ ?_ ?_ hr
    · intro j
      by_cases hj : j = i
      · simp [hj]
      replace hind := congr_fun hind j
      convert hind using 1
      · simp [Set.indicator_apply, hj]
      · simp [Set.indicator_apply, hj, w', AffineMap.lineMap_apply_module]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]

lemma exists_affineCombination_eq_smul_eq_of_fintype [Fintype ι] {p : ι → P}
    (hp : AffineIndependent k p) {s : Set ι} (hs : s.Nonempty) {w : s → ι → k}
    (hw : ∀ i, ∑ j, w i j = 1) {p' : P}
    (hp' : ∀ i : s, p' ∈ line[k, p i, Finset.univ.affineCombination k p (w i)]) :
    ∃ w' : ι → k, (∑ j, w' j = 1) ∧ Finset.univ.affineCombination k p w' = p' ∧
      ∀ i : s, ∃ r, ∀ j, r * Set.indicator {(i : ι)}ᶜ (w i) j =
        Set.indicator {(i : ι)}ᶜ w' j := by
  classical
  obtain ⟨w'', fs'', hw'', hw''p', hi⟩ := hp.exists_affineCombination_eq_smul_eq hs hw hp'
  refine ⟨Set.indicator fs'' w'', ?_, ?_, ?_⟩
  · rw [← hw'']
    exact Finset.sum_indicator_subset _ (by simp)
  · rw [← hw''p']
    exact (Finset.affineCombination_indicator_subset _ _ (by simp)).symm
  · intro i
    obtain ⟨r, hr⟩ := hi i
    refine ⟨r, fun j ↦ ?_⟩
    convert hr j using 1
    · simp [Set.indicator_apply]
    · by_cases hj : j = (i : ι) <;> simp [Set.indicator_apply, hj]

end AffineIndependent

namespace Affine.Triangle

section CommRing

variable [CommRing k] [NoZeroDivisors k] [AddCommGroup V] [Module k V] [AffineSpace V P]

end CommRing

section Field

variable [Field k] [AddCommGroup V] [Module k V] [AffineSpace V P]

-- DISSOLVED: prod_div_one_sub_eq_one_of_mem_line_point_lineMap

end Field

end Affine.Triangle
