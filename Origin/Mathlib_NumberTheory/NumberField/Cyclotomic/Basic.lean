/-
Extracted from NumberTheory/NumberField/Cyclotomic/Basic.lean
Genuine: 8 of 9 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ring of integers of cyclotomic fields
We gather results about cyclotomic extensions of `ℚ`. In particular, we compute the ring of
integers of a cyclotomic extension of `ℚ`.

## Main results
* `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`: if `K` is a cyclotomic
  extension of `ℚ`, then `adjoin ℤ {ζ}` is the integral closure of `ℤ` in `K`.
* `IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure`: the integral
  closure of `ℤ` inside `CyclotomicField n ℚ` is `CyclotomicRing n ℤ ℚ`.
* `IsCyclotomicExtension.Rat.discr` and related results: the absolute discriminant
  of cyclotomic fields.
-/

universe u

open Algebra IsCyclotomicExtension Polynomial NumberField

open scoped Cyclotomic Nat

variable {p k n : ℕ} {K : Type u} [Field K] {ζ : K} [hp : Fact p.Prime]

namespace IsCyclotomicExtension.Rat

variable [CharZero K]

variable (k K) in

-- DISSOLVED: finrank

theorem discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hk : p ^ (k + 1) ≠ 2) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis =
      (-1) ^ ((p ^ (k + 1)).totient / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  rw [← discr_prime_pow_ne_two hζ (cyclotomic.irreducible_rat (NeZero.pos _)) hk]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

theorem discr_odd_prime' [IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) (hodd : p ≠ 2) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  rw [← discr_odd_prime hζ (cyclotomic.irreducible_rat hp.out.pos) hodd]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

theorem discr_prime_pow' [IsCyclotomicExtension {p ^ k} ℚ K] (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis =
      (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  rw [← discr_prime_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

theorem discr_prime_pow_eq_unit_mul_pow' [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    ∃ (u : ℤˣ) (n : ℕ), discr ℚ (hζ.subOnePowerBasis ℚ).basis = u * p ^ n := by
  rw [hζ.discr_zeta_eq_discr_zeta_sub_one.symm]
  exact discr_prime_pow_eq_unit_mul_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))

theorem isIntegralClosure_adjoin_singleton_of_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : IsIntegralClosure (adjoin ℤ ({ζ} : Set K)) ℤ K := by
  refine ⟨Subtype.val_injective, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact
      IsIntegral.algebraMap
        ((le_integralClosure_iff_isIntegral.1
          (adjoin_le_integralClosure (hζ.isIntegral (NeZero.pos _)))).isIntegral _)
  let B := hζ.subOnePowerBasis ℚ
  have hint : IsIntegral ℤ B.gen := (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one
  -- This can't be a `local instance` because it has metavariables.
  letI := IsCyclotomicExtension.finiteDimensional {p ^ k} ℚ K
  have H := discr_mul_isIntegral_mem_adjoin ℚ hint h
  obtain ⟨u, n, hun⟩ := discr_prime_pow_eq_unit_mul_pow' hζ
  rw [hun] at H
  replace H := Subalgebra.smul_mem _ H u.inv
  rw [← smul_assoc, ← smul_mul_assoc, Units.inv_eq_val_inv, zsmul_eq_mul, ← Int.cast_mul,
    Units.inv_mul, Int.cast_one, one_mul, smul_def, map_pow] at H
  cases k
  · haveI : IsCyclotomicExtension {1} ℚ K := by simpa using hcycl
    have : x ∈ (⊥ : Subalgebra ℚ K) := by
      rw [singleton_one ℚ K]
      exact mem_top
    obtain ⟨y, rfl⟩ := mem_bot.1 this
    replace h := (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).1 h
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hz, ← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ _
  · have hmin : (minpoly ℤ B.gen).IsEisensteinAt (Submodule.span ℤ {(p : ℤ)}) := by
      have h₁ := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
      have h₂ := hζ.minpoly_sub_one_eq_cyclotomic_comp (cyclotomic.irreducible_rat (NeZero.pos _))
      rw [IsPrimitiveRoot.subOnePowerBasis_gen] at h₁
      #adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
      we needed to change the next line from `rw` to `erw`. -/
      erw [h₁, ← map_cyclotomic_int, show Int.castRingHom ℚ = algebraMap ℤ ℚ by rfl,
        show X + 1 = map (algebraMap ℤ ℚ) (X + 1) by simp, ← map_comp] at h₂
      rw [IsPrimitiveRoot.subOnePowerBasis_gen,
        map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int h₂]
      exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p _
    refine
      adjoin_le ?_
        (mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (n := n)
          (Nat.prime_iff_prime_int.1 hp.out) hint h (by simpa using H) hmin)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact Subalgebra.sub_mem _ (self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)

theorem isIntegralClosure_adjoin_singleton_of_prime [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) : IsIntegralClosure (adjoin ℤ ({ζ} : Set K)) ℤ K := by
  rw [← pow_one p] at hζ hcycl
  exact isIntegralClosure_adjoin_singleton_of_prime_pow hζ

set_option backward.isDefEq.respectTransparency false in

theorem cyclotomicRing_isIntegralClosure_of_prime_pow :
    IsIntegralClosure (CyclotomicRing (p ^ k) ℤ ℚ) ℤ (CyclotomicField (p ^ k) ℚ) := by
  have hζ := zeta_spec (p ^ k) ℚ (CyclotomicField (p ^ k) ℚ)
  refine ⟨IsFractionRing.injective _ _, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singleton_subset_iff, Set.mem_setOf_eq]
    exact hζ.pow_eq_one
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap ((IsCyclotomicExtension.integral {p ^ k} ℤ _).isIntegral _)

theorem cyclotomicRing_isIntegralClosure_of_prime :
    IsIntegralClosure (CyclotomicRing p ℤ ℚ) ℤ (CyclotomicField p ℚ) := by
  rw [← pow_one p]
  exact cyclotomicRing_isIntegralClosure_of_prime_pow

end IsCyclotomicExtension.Rat

section PowerBasis

open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

section CharZero

variable [CharZero K]
