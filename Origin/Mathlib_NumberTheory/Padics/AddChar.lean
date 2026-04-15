/-
Extracted from NumberTheory/Padics/AddChar.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Additive characters of `ℤ_[p]`

We show that for any complete, ultrametric normed `ℤ_[p]`-algebra `R`, there is a bijection between
continuous additive characters `ℤ_[p] → R` and topologically nilpotent elements of `R`, given by
sending `κ` to the element `κ 1 - 1`. This is used to define the Mahler transform for `p`-adic
measures.

Note that if the norm on `R` is not strictly multiplicative, then the condition that `κ 1 - 1` be
topologically nilpotent is strictly weaker than assuming `‖κ 1 - 1‖ < 1`, although they are
equivalent if `NormMulClass R` holds.

## Main definitions and theorems:

* `addChar_of_value_at_one`: given a topologically nilpotent `r : R`, construct a continuous
  additive character of `ℤ_[p]` mapping `1` to `1 + r`.
* `continuousAddCharEquiv`: for any complete, ultrametric normed `ℤ_[p]`-algebra `R`, the map
  `addChar_of_value_at_one` defines a bijection between continuous additive characters `ℤ_[p] → R`
  and topologically nilpotent elements of `R`.
* `continuousAddCharEquiv_of_norm_mul`: if the norm on `R` is strictly multiplicative (not just
  sub-multiplicative), then `addChar_of_value_at_one` is a bijection between continuous additive
  characters `ℤ_[p] → R` and elements of `R` with `‖r‖ < 1`.

## TODO:

* Show that the above equivalences are homeomorphisms, for appropriate choices of the topology.
-/

open scoped fwdDiff

open Filter Topology

variable {p : ℕ} [Fact p.Prime]

variable {R : Type*} [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R]

lemma AddChar.tendsto_eval_one_sub_pow {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) :
    Tendsto (fun n ↦ (κ 1 - 1) ^ n) atTop (𝓝 0) := by
  refine (PadicInt.fwdDiff_tendsto_zero ⟨κ, hκ⟩).congr fun n ↦ ?_
  simpa only [AddChar.map_zero_eq_one, mul_one] using fwdDiff_addChar_eq κ 0 1 n

namespace PadicInt

variable [CompleteSpace R]

noncomputable def addChar_of_value_at_one (r : R) (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    AddChar ℤ_[p] R where
  toFun := mahlerSeries (r ^ ·)
  map_zero_eq_one' := by
    rw [← Nat.cast_zero, mahlerSeries_apply_nat hr le_rfl, zero_add, Finset.sum_range_one,
      Nat.choose_self, pow_zero, one_smul]
  map_add_eq_mul' a b := by
    let F : C(ℤ_[p], R) := mahlerSeries (r ^ ·)
    change F (a + b) = F a * F b
    -- It is fiddly to show directly that `F (a + b) = F a * F b` for general `a, b`,
    -- so we prove it for `a, b ∈ ℕ` directly, and then deduce it for all `a, b` by continuity.
    have hF (n : ℕ) : F n = (r + 1) ^ n := by
      rw [mahlerSeries_apply_nat hr le_rfl, (Commute.one_right _).add_pow]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [one_pow, mul_one, nsmul_eq_mul, Nat.cast_comm]
    refine congr_fun ((denseRange_natCast.prodMap denseRange_natCast).equalizer
      ((map_continuous F).comp continuous_add)
      (continuous_mul.comp (map_continuous <| F.prodMap F)) (funext fun ⟨m, n⟩ ↦ ?_)) (a, b)
    simp [← Nat.cast_add, hF, ContinuousMap.prodMap_apply, pow_add]
