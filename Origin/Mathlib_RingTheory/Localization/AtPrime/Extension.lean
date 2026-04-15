/-
Extracted from RingTheory/Localization/AtPrime/Extension.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Primes in an extension of localization at prime

Let `R ⊆ S` be an extension of Dedekind domains and `p` be a prime ideal of `R`. Let `Rₚ` be the
localization of `R` at the complement of `p` and `Sₚ` the localization of `S` at the (image)
of the complement of `p`.

In this file, we study the relation between the (nonzero) prime ideals of `Sₚ` and the prime
ideals of `S` above `p`. In particular, we prove that (under suitable conditions) they are in
bijection and that the residual degree and ramification index are preserved by this bijection.

## Main definitions and results

- `IsLocalization.AtPrime.mem_primesOver_of_isPrime`: The nonzero prime ideals of `Sₚ` are
  primes over the maximal ideal of `Rₚ`.

- `IsLocalization.AtPrime.equivQuotientMapOfIsMaximal`: `S ⧸ P ≃+* Sₚ ⧸ P·Sₚ` where
  `P` is a maximal ideal of `S` above `p`.

- `IsDedekindDomain.primesOverEquivPrimesOver`: the bijection between the primes over
  `p` in `S` and the primes over the maximal ideal of `Rₚ` in `Sₚ`.

- `IsDedekindDomain.primesOverEquivPrimesOver_inertiagDeg_eq`: the bijection
  `primesOverEquivPrimesOver` preserves the inertia degree.

- `IsDedekindDomain.primesOverEquivPrimesOver_ramificationIdx_eq`: the bijection
  `primesOverEquivPrimesOver` preserves the ramification index.

-/

open Algebra Module IsLocalRing Ideal Localization.AtPrime

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
  (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
  (Sₚ : Type*) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization (algebraMapSubmonoid S p.primeCompl) Sₚ]
  [Algebra Rₚ Sₚ] (P : Ideal S) [hPp : P.LiesOver p]

namespace IsLocalization.AtPrime

theorem mem_primesOver_of_isPrime {Q : Ideal Sₚ} [Q.IsMaximal] [Algebra.IsIntegral Rₚ Sₚ] :
    Q ∈ (maximalIdeal Rₚ).primesOver Sₚ := by
  refine ⟨inferInstance, ?_⟩
  rw [liesOver_iff, ← eq_maximalIdeal]
  exact IsMaximal.under Rₚ Q

theorem liesOver_comap_of_liesOver {T : Type*} [CommRing T] [Algebra R T] [Algebra Rₚ T]
    [Algebra S T] [IsScalarTower R S T] [IsScalarTower R Rₚ T] (Q : Ideal T)
    [Q.LiesOver (maximalIdeal Rₚ)] : (comap (algebraMap S T) Q).LiesOver p := by
  have : Q.LiesOver p := by
    have : (maximalIdeal Rₚ).LiesOver p := liesOver_maximalIdeal Rₚ p _
    exact LiesOver.trans Q (IsLocalRing.maximalIdeal Rₚ) p
  exact comap_liesOver Q p <| IsScalarTower.toAlgHom R S T

include p in

theorem liesOver_map_of_liesOver [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
    [P.IsPrime] :
    (P.map (algebraMap S Sₚ)).LiesOver (IsLocalRing.maximalIdeal Rₚ) := by
  rw [liesOver_iff, eq_comm, ← map_eq_maximalIdeal p, over_def P p]
  exact under_map_eq_map_under _
    (over_def P p ▸ map_eq_maximalIdeal p Rₚ ▸ maximalIdeal.isMaximal Rₚ)
    (isPrime_map_of_liesOver S p Sₚ P).ne_top

attribute [local instance] Ideal.Quotient.field

include p in

theorem exists_algebraMap_quot_eq_of_mem_quot [P.IsMaximal]
    (x : Sₚ ⧸ P.map (algebraMap S Sₚ)) :
    ∃ a, (algebraMap S (Sₚ ⧸ P.map (algebraMap S Sₚ))) a = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (algebraMapSubmonoid S p.primeCompl) x
  obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := P) (Ideal.Quotient.mk P s)⁻¹
  simp only [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), Quotient.algebraMap_eq, RingHom.comp_apply]
  use x * s'
  rw [← sub_eq_zero, ← map_sub, Quotient.eq_zero_iff_mem]
  have h₀ : (P.map (algebraMap S Sₚ)).IsPrime := isPrime_map_of_liesOver S p Sₚ P
  have h₁ : s.1 ∉ P := (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver P p) s.prop
  have h₂ : algebraMap S Sₚ s ∉ Ideal.map (algebraMap S Sₚ) P := by
    rwa [← mem_comap, comap_map_eq_self_of_isMaximal _ h₀.ne_top]
  refine (h₀.mem_or_mem ?_).resolve_left h₂
  rw [mul_sub, mul_mk'_eq_mk'_of_mul, mk'_mul_cancel_left, ← map_mul, ← map_sub, ← mem_comap,
    comap_map_eq_self_of_isMaximal _ IsPrime.ne_top', ← Ideal.Quotient.eq, map_mul, map_mul, hs,
    mul_comm, inv_mul_cancel_right₀ (Quotient.eq_zero_iff_mem.not.mpr h₁)]

noncomputable def equivQuotientMapOfIsMaximal [p.IsPrime] [P.IsMaximal] :
    S ⧸ P ≃+* Sₚ ⧸ P.map (algebraMap S Sₚ) :=
  .trans
    (Ideal.quotEquivOfEq (by
      rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), ← RingHom.comap_ker, Quotient.algebraMap_eq,
        mk_ker, comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top]))
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ _))
      fun x ↦ exists_algebraMap_quot_eq_of_mem_quot p Sₚ P x)
