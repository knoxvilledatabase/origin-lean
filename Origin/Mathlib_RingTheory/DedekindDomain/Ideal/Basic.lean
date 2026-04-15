/-
Extracted from RingTheory/DedekindDomain/Ideal/Basic.lean
Genuine: 12 of 32 | Dissolved: 3 | Infrastructure: 17
-/
import Origin.Core

/-!
# Dedekind domains and invertible ideals

In this file, we show a ring is a Dedekind domain iff all fractional ideals are invertible,
and prove instances such as the unique factorization of ideals.
Further results on the structure of ideals in a Dedekind domain are found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`.

## Main definitions

- `IsDedekindDomainInv` alternatively defines a Dedekind domain as an integral domain where
  every nonzero fractional ideal is invertible.
- `isDedekindDomainInv_iff` shows that this does not depend on the choice of field of
  fractions.

## Main results:

- `isDedekindDomain_iff_isDedekindDomainInv`
- `Ideal.uniqueFactorizationMonoid`

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

section Inverse

section IsDedekindDomainInv

variable [IsDomain A]

def IsDedekindDomainInv : Prop :=
  ∀ I ≠ (⊥ : FractionalIdeal A⁰ (FractionRing A)), I * I⁻¹ = 1

open FractionalIdeal

variable {R A K}

theorem isDedekindDomainInv_iff [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomainInv A ↔ ∀ I ≠ (⊥ : FractionalIdeal A⁰ K), I * I⁻¹ = 1 := by
  let h : FractionalIdeal A⁰ (FractionRing A) ≃+* FractionalIdeal A⁰ K :=
    FractionalIdeal.mapEquiv (FractionRing.algEquiv A K)
  refine h.toEquiv.forall_congr (fun {x} => ?_)
  rw [← h.toEquiv.apply_eq_iff_eq]
  simp [h]

theorem FractionalIdeal.adjoinIntegral_eq_one_of_isUnit [Algebra A K] [IsFractionRing A K] (x : K)
    (hx : IsIntegral A x) (hI : IsUnit (adjoinIntegral A⁰ x hx)) : adjoinIntegral A⁰ x hx = 1 := by
  set I := adjoinIntegral A⁰ x hx
  have mul_self : IsIdempotentElem I := by
    apply coeToSubmodule_injective
    simp only [coe_mul, adjoinIntegral_coe, I]
    rw [(Algebra.adjoin A {x}).isIdempotentElem_toSubmodule]
  convert congr_arg (· * I⁻¹) mul_self <;>
    simp only [(mul_inv_cancel_iff_isUnit K).mpr hI, mul_assoc, mul_one]

namespace IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K] (h : IsDedekindDomainInv A) {I J : FractionalIdeal A⁰ K}

include h

-- DISSOLVED: commGroupWithZero

open Ring

theorem isDedekindDomain : IsDedekindDomain A :=
  { h.isNoetherianRing, h.dimensionLEOne, h.integrallyClosed with }

end IsDedekindDomainInv

end IsDedekindDomainInv

variable [Algebra A K] [IsFractionRing A K]

variable {A K}

theorem one_mem_inv_coe_ideal [IsDomain A] {I : Ideal A} (hI : I ≠ ⊥) :
    (1 : K) ∈ (I : FractionalIdeal A⁰ K)⁻¹ := by
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hI)]
  intro y hy
  rw [one_mul]
  exact FractionalIdeal.coeIdeal_le_one hy

theorem exists_multiset_prod_cons_le_and_prod_not_le [IsDedekindDomain A] (hNF : ¬IsField A)
    {I M : Ideal A} (hI0 : I ≠ ⊥) (hIM : I ≤ M) [hM : M.IsMaximal] :
    ∃ Z : Multiset (PrimeSpectrum A),
      (M ::ₘ Z.map PrimeSpectrum.asIdeal).prod ≤ I ∧
        ¬Multiset.prod (Z.map PrimeSpectrum.asIdeal) ≤ I := by
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    wellFounded_lt.has_min
      {Z | (Z.map PrimeSpectrum.asIdeal).prod ≤ I ∧ (Z.map PrimeSpectrum.asIdeal).prod ≠ ⊥}
      ⟨Z₀, hZ₀.1, hZ₀.2⟩
  obtain ⟨_, hPZ', hPM⟩ := hM.isPrime.multiset_prod_le.mp (hZI.trans hIM)
  -- Then in fact there is a `P ∈ Z` with `P ≤ M`.
  obtain ⟨P, hPZ, rfl⟩ := Multiset.mem_map.mp hPZ'
  classical
    have := Multiset.map_erase PrimeSpectrum.asIdeal (fun _ _ => PrimeSpectrum.ext) P Z
    obtain ⟨hP0, hZP0⟩ : P.asIdeal ≠ ⊥ ∧ ((Z.erase P).map PrimeSpectrum.asIdeal).prod ≠ ⊥ := by
      rwa [Ne, ← Multiset.cons_erase hPZ', Multiset.prod_cons, Ideal.mul_eq_bot, not_or, ←
        this] at hprodZ
    -- By maximality of `P` and `M`, we have that `P ≤ M` implies `P = M`.
    have hPM' := (P.isPrime.isMaximal hP0).eq_of_le hM.ne_top hPM
    subst hPM'
    -- By minimality of `Z`, erasing `P` from `Z` is exactly what we need.
    refine ⟨Z.erase P, ?_, ?_⟩
    · convert hZI
      rw [this, Multiset.cons_erase hPZ']
    · refine fun h => h_eraseZ (Z.erase P) ⟨h, ?_⟩ (Multiset.erase_lt.mpr hPZ)
      exact hZP0

namespace FractionalIdeal

variable [IsDedekindDomain A] {I : Ideal A}

open Ideal

theorem mul_inv_cancel_of_le_one (hI0 : I ≠ ⊥) (hI : (I * (I : FractionalIdeal A⁰ K)⁻¹)⁻¹ ≤ 1) :
    I * (I : FractionalIdeal A⁰ K)⁻¹ = 1 := by
  -- We'll show a contradiction with `exists_notMem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, (J : FractionalIdeal A⁰ K) = I * (I : FractionalIdeal A⁰ K)⁻¹ :=
    le_one_iff_exists_coeIdeal.mp mul_one_div_le_one
  by_cases hJ0 : J = ⊥
  · subst hJ0
    refine absurd ?_ hI0
    rw [eq_bot_iff, ← coeIdeal_le_coeIdeal K, hJ]
    exact coe_ideal_le_self_mul_inv K I
  by_cases hJ1 : J = ⊤
  · rw [← hJ, hJ1, coeIdeal_top]
  exact (not_inv_le_one_of_ne_bot (K := K) hJ0 hJ1 (hJ ▸ hI)).elim

theorem coe_ideal_mul_inv (I : Ideal A) (hI0 : I ≠ ⊥) : I * (I : FractionalIdeal A⁰ K)⁻¹ = 1 := by
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0
  by_cases hJ0 : I * (I : FractionalIdeal A⁰ K)⁻¹ = 0
  · rw [hJ0, inv_zero']; exact zero_le _
  intro x hx
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices x ∈ integralClosure A K by
    rwa [IsIntegrallyClosed.integralClosure_eq_bot, Algebra.mem_bot, Set.mem_range,
      ← mem_one_iff] at this
  -- For that, we'll find a subalgebra that is f.g. as a module and contains `x`.
  -- `A` is a Noetherian ring, so we just need to find a subalgebra between `{x}` and `I⁻¹`.
  rw [mem_integralClosure_iff_mem_fg]
  have x_mul_mem : ∀ b ∈ (I⁻¹ : FractionalIdeal A⁰ K), x * b ∈ (I⁻¹ : FractionalIdeal A⁰ K) := by
    intro b hb
    rw [mem_inv_iff (coeIdeal_ne_zero.mpr hI0)]
    rw [mem_inv_iff hJ0] at hx
    simp_rw [mul_assoc, mul_comm b]
    exact fun y hy ↦ hx _ (mul_mem_mul hy hb)
  -- It turns out the subalgebra consisting of all `p(x)` for `p : A[X]` works.
  refine ⟨AlgHom.range (Polynomial.aeval x : A[X] →ₐ[A] K),
    isNoetherian_submodule.mp (isNoetherian (I : FractionalIdeal A⁰ K)⁻¹) _ fun y hy => ?_,
    ⟨Polynomial.X, Polynomial.aeval_X x⟩⟩
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hy
  rw [Polynomial.aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  clear hi
  induction i with
  | zero => rw [pow_zero]; exact one_mem_inv_coe_ideal hI0
  | succ i ih => rw [pow_succ']; exact x_mul_mem _ ih

-- INSTANCE (free from Core): semifield

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- DISSOLVED: mul_left_strictMono

-- DISSOLVED: mul_right_strictMono

-- INSTANCE (free from Core): [IsDedekindDomain

end FractionalIdeal

theorem isDedekindDomain_iff_isDedekindDomainInv [IsDomain A] :
    IsDedekindDomain A ↔ IsDedekindDomainInv A :=
  ⟨fun _h _I => mul_inv_cancel₀, fun h => h.isDedekindDomain⟩

end Inverse

section IsDedekindDomain

variable {R A}

variable [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal Ideal

-- INSTANCE (free from Core): Ideal.isCancelMulZero

-- INSTANCE (free from Core): Ideal.isDomain

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

theorem Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J ≤ I :=
  ⟨Ideal.le_of_dvd, fun h => by
    by_cases hI : I = ⊥
    · have hJ : J = ⊥ := by rwa [hI, ← eq_bot_iff] at h
      rw [hI, hJ]
    have hI' : (I : FractionalIdeal A⁰ (FractionRing A)) ≠ 0 := coeIdeal_ne_zero.mpr hI
    have : (I : FractionalIdeal A⁰ (FractionRing A))⁻¹ * J ≤ 1 := by
      rw [← inv_mul_cancel₀ hI']; gcongr
    obtain ⟨H, hH⟩ := le_one_iff_exists_coeIdeal.mp this
    use H
    refine coeIdeal_injective (show (J : FractionalIdeal A⁰ (FractionRing A)) = ↑(I * H) from ?_)
    rw [coeIdeal_mul, hH, ← mul_assoc, mul_inv_cancel₀ hI', one_mul]⟩

theorem Ideal.liesOver_iff_dvd_map [Algebra R A] {p : Ideal R} {P : Ideal A} (hP : P ≠ ⊤)
    [p.IsMaximal] :
    P.LiesOver p ↔ P ∣ Ideal.map (algebraMap R A) p := by
  rw [liesOver_iff, dvd_iff_le, under_def, map_le_iff_le_comap,
    IsCoatom.le_iff_eq (by rwa [← isMaximal_def]) (comap_ne_top _ hP), eq_comm]

theorem Ideal.dvdNotUnit_iff_lt {I J : Ideal A} : DvdNotUnit I J ↔ J < I :=
  ⟨fun ⟨hI, H, hunit, hmul⟩ =>
    lt_of_le_of_ne (Ideal.dvd_iff_le.mp ⟨H, hmul⟩)
      (mt
        (fun h =>
          have : H = 1 := mul_left_cancel₀ hI (by rw [← hmul, h, mul_one])
          show IsUnit H from this.symm ▸ isUnit_one)
        hunit),
    fun h =>
    dvdNotUnit_of_dvd_of_not_dvd (Ideal.dvd_iff_le.mpr (le_of_lt h))
      (mt Ideal.dvd_iff_le.mp (not_le_of_gt h))⟩

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): Ideal.uniqueFactorizationMonoid

-- INSTANCE (free from Core): Ideal.normalizationMonoid

end IsDedekindDomain
