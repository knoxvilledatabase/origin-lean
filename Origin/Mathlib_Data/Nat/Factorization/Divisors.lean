/-
Extracted from Data/Nat/Factorization/Divisors.lean
Genuine: 5 of 8 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results about divisors and factorizations
-/

open Finsupp

namespace Nat

-- DISSOLVED: coe_divisors_eq_prod_pow_le_factorization

-- DISSOLVED: divisors_eq_image_Iic_factorization_prod_pow

theorem Iic_factorization_prod_pow_injective (n : ℕ) :
    (·.val.prod (· ^ ·) : Finset.Iic n.factorization → _).Injective := by
  grind [Function.Injective, factorization_prod_pow_eq_self_of_le_factorization]

-- DISSOLVED: divisors_eq_map_attach_Iic_factorization_prod_pow

theorem coe_properDivisors_eq_prod_pow_lt_factorization {n : ℕ} :
    n.properDivisors = { f.prod (· ^ ·) | f < n.factorization } := by
  by_cases hn : n = 0
  · simp [hn]
  refine Set.ext fun k ↦ ⟨fun h ↦ ?_, fun ⟨f, hlt, h⟩ ↦ ?_⟩
  · have ⟨hdvd, hlt⟩ := mem_properDivisors.mp h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
    refine ⟨_, ?_, prod_factorization_pow_eq_self hk⟩
    apply lt_of_le_of_ne <| factorization_le_iff_dvd hk hn |>.mpr hdvd
    exact mt (Nat.eq_of_factorization_eq' hk hn) hlt.ne
  · have : k ∣ n := by
      rw [← h, ← prod_factorization_pow_eq_self hn]
      apply prod_dvd_prod_of_subset_of_dvd <| support_mono hlt.le
      exact fun p _ ↦ Nat.pow_dvd_pow p <| hlt.le p
    refine mem_properDivisors.mpr ⟨this, lt_of_le_of_ne (le_of_dvd (Nat.pos_of_ne_zero hn) this) ?_⟩
    suffices k.factorization = f from (this ▸ hlt.ne <| congrArg _ ·)
    exact h ▸ factorization_prod_pow_eq_self_of_le_factorization hlt.le

theorem properDivisors_eq_image_Iio_factorization_prod_pow {n : ℕ} :
    n.properDivisors = (Finset.Iio n.factorization).image (·.prod (· ^ ·)) := by
  apply Finset.coe_inj.mp
  grind [coe_properDivisors_eq_prod_pow_lt_factorization]

theorem Iio_factorization_prod_pow_injective (n : ℕ) :
    (·.val.prod (· ^ ·) : Finset.Iio n.factorization → _).Injective := by
  grind [Function.Injective, factorization_prod_pow_eq_self_of_le_factorization]

theorem properDivisors_eq_map_attach_Iio_factorization_prod_pow {n : ℕ} :
    n.properDivisors = (Finset.Iio n.factorization).attach.map
      ⟨(·.val.prod (· ^ ·)), Iio_factorization_prod_pow_injective n⟩ := by
  rw [Finset.map_eq_image]
  change _ = (Finset.Iio n.factorization).attach.image ((·.prod (· ^ ·)) ∘ Subtype.val)
  rw [← Finset.image_image, Finset.attach_image_val]
  exact properDivisors_eq_image_Iio_factorization_prod_pow

end Nat
