/-
Extracted from RingTheory/HahnSeries/HEval.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Evaluation of power series in Hahn Series

We describe a class of ring homomorphisms from formal power series to Hahn series,
given by substitution of the generating variable to an element of strictly positive order.

## Main Definitions
* `HahnSeries.SummableFamily.powerSeriesFamily`: A summable family of Hahn series whose elements
  are non-negative powers of a fixed positive-order Hahn series multiplied by the coefficients of a
  formal power series.
* `PowerSeries.heval`: The `R`-algebra homomorphism from `PowerSeries σ R` to `R⟦Γ⟧` that
  takes `X` to a fixed positive-order Hahn Series and extends to formal infinite sums.

## TODO
* `MvPowerSeries.heval`: An `R`-algebra homomorphism from `MvPowerSeries σ R` to `R⟦Γ⟧`
  (for finite σ) taking each `X i` to a positive order Hahn Series.

-/

open Finset Function

noncomputable section

variable {Γ Γ' R V α β σ : Type*}

namespace HahnSeries

namespace SummableFamily

section PowerSeriesFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

variable [CommRing V] [Algebra R V]

abbrev powerSeriesFamily (x : V⟦Γ⟧) (f : PowerSeries R) : SummableFamily Γ V ℕ :=
  smulFamily (fun n => f.coeff n) (powers x)

theorem powerSeriesFamily_of_not_orderTop_pos {x : V⟦Γ⟧} (hx : ¬ 0 < x.orderTop)
    (f : PowerSeries R) :
    powerSeriesFamily x f = powerSeriesFamily 0 f := by
  ext n g
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

theorem powerSeriesFamily_of_orderTop_pos {x : V⟦Γ⟧} (hx : 0 < x.orderTop)
    (f : PowerSeries R) (n : ℕ) :
    powerSeriesFamily x f n = f.coeff n • x ^ n := by
  simp [hx]

theorem powerSeriesFamily_hsum_zero (f : PowerSeries R) :
    (powerSeriesFamily 0 f).hsum = f.constantCoeff • (1 : V⟦Γ⟧) := by
  ext g
  by_cases hg : g = 0
  · simp only [hg, coeff_hsum]
    rw [finsum_eq_single _ 0 (fun n hn ↦ by simp [hn])]
    simp
  · rw [coeff_hsum, finsum_eq_zero_of_forall_eq_zero
      fun n ↦ (by by_cases hn : n = 0 <;> simp [hg, hn])]
    simp [hg]

theorem powerSeriesFamily_add {x : V⟦Γ⟧} (f g : PowerSeries R) :
    powerSeriesFamily x (f + g) = powerSeriesFamily x f + powerSeriesFamily x g := by
  ext1 n
  by_cases hx : 0 < x.orderTop <;> · simp [hx, add_smul]

theorem powerSeriesFamily_smul {x : V⟦Γ⟧} (f : PowerSeries R) (r : R) :
    powerSeriesFamily x (r • f) = HahnSeries.single (0 : Γ) r • powerSeriesFamily x f := by
  ext1 n
  simp [mul_smul]

theorem support_powerSeriesFamily_subset {x : V⟦Γ⟧} (a b : PowerSeries R) (g : Γ) :
    ((powerSeriesFamily x (a * b)).coeff g).support ⊆
    (((powerSeriesFamily x a).mul (powerSeriesFamily x b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  by_cases h : 0 < x.orderTop
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    have he : ∃ c ∈ antidiagonal n, (PowerSeries.coeff c.1) a • (PowerSeries.coeff c.2) b •
        ((powers x) n).coeff g ≠ 0 := by
      refine exists_ne_zero_of_sum_ne_zero ?_
      simpa [PowerSeries.coeff_mul, sum_smul, mul_smul, h] using hn
    simp only [powers_of_orderTop_pos h, mem_antidiagonal] at he
    obtain ⟨c, hcn, hc⟩ := he
    simp only [coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    use c
    simp only [mul_toFun, smulFamily_toFun, Function.mem_support, hcn,
      and_true]
    rw [powers_of_orderTop_pos h c.1, powers_of_orderTop_pos h c.2, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, ← pow_add, hcn]
    simp [hc]
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    by_cases hz : n = 0
    · have : g = 0 ∧ (a.constantCoeff * b.constantCoeff) • (1 : V) ≠ 0 := by
        simpa [hz, h] using hn
      simp only [coe_image, Set.mem_image]
      use (0, 0)
      simp [this.2, this.1, h, hz, smul_smul, mul_comm]
    · simp [h, hz] at hn

theorem hsum_powerSeriesFamily_mul {x : V⟦Γ⟧} (a b : PowerSeries R) :
    (powerSeriesFamily x (a * b)).hsum =
    ((powerSeriesFamily x a).mul (powerSeriesFamily x b)).hsum := by
  by_cases h : 0 < x.orderTop;
  · ext g
    simp only [coeff_hsum_eq_sum, smulFamily_toFun, h, powers_of_orderTop_pos,
      HahnSeries.coeff_smul, mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [sum_subset (support_powerSeriesFamily_subset a b g)
      (fun i hi his ↦ by simpa [h, PowerSeries.coeff_mul, sum_smul] using his)]
    simp only [coeff_support, mul_toFun, smulFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, HahnSeries.coeff_smul, PowerSeries.coeff_mul, sum_smul]
    rw [sum_sigma']
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) (fun _ _ _ _ => by simp) ?_ ?_
      (fun _ _ => by simp [smul_smul, mul_comm, pow_add])).symm
    · intro ij hij
      simp only [coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_coe,
        mem_antidiagonal, and_true]
      use ij.1, ij.2
      simp_all
    · intro i hi his
      have hisc : ∀ j k : ℕ, ⟨j + k, (j, k)⟩ = i → (PowerSeries.coeff k) b •
          (PowerSeries.coeff j a • (x ^ j * x ^ k).coeff g) = 0 := by
        intro m n
        contrapose!
        simp only [powers_of_orderTop_pos h, Set.Finite.coe_toFinset, Set.mem_image,
          Function.mem_support, ne_eq, Prod.exists, not_exists, not_and] at his
        exact his m n
      simp only [mem_sigma, mem_antidiagonal] at hi
      rw [mul_comm ((PowerSeries.coeff i.snd.1) a), ← hi.2, mul_smul, pow_add]
      exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)
  · simp only [h, not_false_eq_true, powerSeriesFamily_of_not_orderTop_pos,
      powerSeriesFamily_hsum_zero, map_mul, hsum_mul]
    rw [smul_mul_smul_comm, mul_one]

end PowerSeriesFamily

end SummableFamily

end HahnSeries

namespace PowerSeries

open HahnSeries SummableFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] (x : R⟦Γ⟧)
