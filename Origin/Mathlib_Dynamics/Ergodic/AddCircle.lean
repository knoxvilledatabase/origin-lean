/-
Extracted from Dynamics/Ergodic/AddCircle.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Ergodic maps of the additive circle

This file contains proofs of ergodicity for maps of the additive circle.

## Main definitions:

* `AddCircle.ergodic_zsmul`: given `n : ℤ` such that `1 < |n|`, the self map `y ↦ n • y` on
  the additive circle is ergodic (w.r.t. the Haar measure).
* `AddCircle.ergodic_nsmul`: given `n : ℕ` such that `1 < n`, the self map `y ↦ n • y` on
  the additive circle is ergodic (w.r.t. the Haar measure).
* `AddCircle.ergodic_zsmul_add`: given `n : ℤ` such that `1 < |n|` and `x : AddCircle T`, the
  self map `y ↦ n • y + x` on the additive circle is ergodic (w.r.t. the Haar measure).
* `AddCircle.ergodic_nsmul_add`: given `n : ℕ` such that `1 < n` and `x : AddCircle T`, the
  self map `y ↦ n • y + x` on the additive circle is ergodic (w.r.t. the Haar measure).

-/

open Set Function MeasureTheory MeasureTheory.Measure Filter Metric

open scoped MeasureTheory NNReal ENNReal Topology Pointwise

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

theorem ergodic_zsmul {n : ℤ} (hn : 1 < |n|) : Ergodic fun y : AddCircle T => n • y :=
  { measurePreserving_zsmul volume (abs_pos.mp <| lt_trans zero_lt_one hn) with
    aeconst_set := fun s hs hs' => by
      let u : ℕ → AddCircle T := fun j => ↑((↑1 : ℝ) / ↑(n.natAbs ^ j) * T)
      replace hn : 1 < n.natAbs := by rwa [Int.abs_eq_natAbs, Nat.one_lt_cast] at hn
      have hu₀ : ∀ j, addOrderOf (u j) = n.natAbs ^ j := fun j => by
        convert addOrderOf_div_of_gcd_eq_one (p := T) (m := 1)
          (pow_pos (pos_of_gt hn) j) (gcd_one_left _)
        norm_cast
      have hnu : ∀ j, n ^ j • u j = 0 := fun j => by
        rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hu₀, Int.natCast_pow, Int.natCast_natAbs, ← abs_pow,
          abs_dvd]
      have hu₁ : ∀ j, (u j +ᵥ s : Set _) =ᵐ[volume] s := fun j => by
        rw [vadd_eq_self_of_preimage_zsmul_eq_self hs' (hnu j)]
      have hu₂ : Tendsto (fun j => addOrderOf <| u j) atTop atTop := by
        simp_rw [hu₀]; exact tendsto_pow_atTop_atTop_of_one_lt hn
      rw [eventuallyConst_set']
      exact ae_empty_or_univ_of_forall_vadd_ae_eq_self hs.nullMeasurableSet hu₁ hu₂ }

theorem ergodic_nsmul {n : ℕ} (hn : 1 < n) : Ergodic fun y : AddCircle T => n • y :=
  ergodic_zsmul (by simp [hn] : 1 < |(n : ℤ)|)

theorem ergodic_zsmul_add (x : AddCircle T) {n : ℤ} (h : 1 < |n|) : Ergodic fun y => n • y + x := by
  set f : AddCircle T → AddCircle T := fun y => n • y + x
  let e : AddCircle T ≃ᵐ AddCircle T := MeasurableEquiv.addLeft (DivisibleBy.div x <| n - 1)
  have he : MeasurePreserving e volume volume :=
    measurePreserving_add_left volume (DivisibleBy.div x <| n - 1)
  suffices e ∘ f ∘ e.symm = fun y => n • y by
    rw [← he.ergodic_conjugate_iff, this]; exact ergodic_zsmul h
  replace h : n - 1 ≠ 0 := by
    rw [← abs_one] at h; rw [sub_ne_zero]; exact ne_of_apply_ne _ (ne_of_gt h)
  have hnx : n • DivisibleBy.div x (n - 1) = x + DivisibleBy.div x (n - 1) := by
    conv_rhs => congr; rw [← DivisibleBy.div_cancel x h]
    rw [sub_smul, one_smul, sub_add_cancel]
  ext y
  simp only [f, e, hnx, MeasurableEquiv.coe_addLeft, MeasurableEquiv.symm_addLeft, comp_apply,
    smul_add, zsmul_neg', neg_smul, neg_add_rev]
  abel

theorem ergodic_nsmul_add (x : AddCircle T) {n : ℕ} (h : 1 < n) : Ergodic fun y => n • y + x :=
  ergodic_zsmul_add x (by simp [h] : 1 < |(n : ℤ)|)

end AddCircle
