/-
Extracted from RingTheory/ZariskisMainTheorem.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Algebraic Zariski's Main Theorem

The statement of Zariski's main theorem is the following:
Given a finite type `R`-algebra `S`, and `p` a prime of `S` such that `S` is quasi-finite at `R`,
then there exists a `f ∉ p` such that `S[1/f]` is isomorphic to `R'[1/f]` where `R'` is the integral
closure of `R` in `S`.

We follow https://stacks.math.columbia.edu/tag/00PI and proceed in the following steps

1. `Algebra.ZariskisMainProperty.of_adjoin_eq_top`:
  The case where `S = R[X]/I`.
  The key is `Polynomial.not_ker_le_map_C_of_surjective_of_quasiFiniteAt`
  which shows that there exists some `g ∈ I` such that some coefficient `gᵢ ∉ p`.
  Then one basically takes `f = gᵢ` and `g` becomes monic in `R[1/gᵢ][X]` up to some minor technical
  issues, and then `S[1/gᵢ]` is basically integral over `R[1/gᵢ]`.
2. `Algebra.ZariskisMainProperty.of_algHom_polynomial`:
  The case where `S` is finite over `R⟨x⟩` for some `x : S`.
  The following key results are first established:
  - `isStronglyTranscendental_mk_radical_conductor`:
    Let `𝔣` be the conductor of `x` (i.e. the largest `S`-ideal in `R⟨x⟩`).
    `x` as an element of `S/√𝔣` is strongly transcendental over `R`.
  - `Algebra.not_quasiFiniteAt_of_stronglyTranscendental`:
    If `S` is reduced, then `x : S` is not strongly transcendental over `R`.
    One first reduces to when `R ⊆ S` are domains, and then to when `R` is integrally closed.
    A going down theorem is now available, which could be applied to
    `Polynomial.map_under_lt_comap_of_quasiFiniteAt`:`(p ∩ R)[X] < p ∩ R<x>` to get a contradiction.

  The second result applied to `S/√𝔣` together with the first result implies that
  `p` does not contain `𝔣`.
  The claim then follows from `Localization.localRingHom_bijective_of_not_conductor_le`.
3. `Algebra.ZariskisMainProperty.of_algHom_mvPolynomial`:
  The case where `S` is finite over `R⟨x₁,...,xₙ⟩`. This is proved using induction on `n`.

## Main definition and results
- `Algebra.ZariskisMainProperty`:
  We say that an `R` algebra `S` satisfies the Zariski's main property at a prime `p` of `S`
  if there exists `r ∉ p` in the integral closure `S'` of `R` in `S`, such that `S'[1/r] = S[1/r]`.
- `Algebra.ZariskisMainProperty.of_finiteType`:
  If `S` is finite type over `R` and quasi-finite at `p`, then `ZariskisMainProperty` holds.
- `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`:
  If `S` is finite type over `R` and quasi-finite at `p`,
  then there exists a subalgebra `S'` of `R` that is finitely generated as an `R`-module,
  and some `r ∈ S'` such that `r ∉ p` and `S'[1/r] = S[1/r]`.
-/

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

open scoped TensorProduct nonZeroDivisors

open Polynomial

namespace Algebra

variable (R) in

def ZariskisMainProperty (p : Ideal S) : Prop :=
  ∃ r : integralClosure R S, r.1 ∉ p ∧ Function.Bijective
    (Localization.awayMap (integralClosure R S).val.toRingHom r)

lemma zariskisMainProperty_iff {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, IsIntegral R r ∧ ∀ x, ∃ m, IsIntegral R (r ^ m * x) := by
  simp only [ZariskisMainProperty, Subtype.exists, ← exists_prop, @exists_comm (_ ∉ p)]
  refine exists₃_congr fun r hr hrp ↦ ?_
  rw [Function.Bijective, and_iff_right
    (by exact IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective),
    Localization.awayMap_surjective_iff]
  simp [mem_integralClosure_iff]

lemma zariskisMainProperty_iff' {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, ∀ x, ∃ m, IsIntegral R (r ^ m * x) := by
  refine zariskisMainProperty_iff.trans (exists_congr fun r ↦ and_congr_right fun hrp ↦
    and_iff_right_of_imp fun H ↦ ?_)
  obtain ⟨n, hn⟩ := H r
  rw [← pow_succ] at hn
  exact (IsIntegral.pow_iff (by simp)).mp hn

lemma zariskisMainProperty_iff_exists_saturation_eq_top {p : Ideal S} :
    ZariskisMainProperty R p ↔ ∃ r ∉ p, ∃ h : IsIntegral R r,
      (integralClosure R S).saturation (.powers r) (by simpa [Submonoid.powers_le]) = ⊤ := by
  simp [zariskisMainProperty_iff, ← top_le_iff, SetLike.le_def,
    Submonoid.mem_powers_iff, mem_integralClosure_iff]

lemma ZariskisMainProperty.restrictScalars [Algebra S T] [IsScalarTower R S T]
    [Algebra.IsIntegral R S] {p : Ideal T} (H : ZariskisMainProperty S p) :
    ZariskisMainProperty R p := by
  rw [zariskisMainProperty_iff'] at H ⊢
  obtain ⟨r, hrp, H⟩ := H
  exact ⟨r, hrp, fun x ↦ ⟨_, isIntegral_trans _ (H x).choose_spec⟩⟩

lemma ZariskisMainProperty.trans [Algebra S T] [IsScalarTower R S T] (p : Ideal T) [p.IsPrime]
    (h₁ : ZariskisMainProperty R (p.under S))
    (h₂ : ∃ r ∉ p.under S, (⊥ : Subalgebra S T).saturation (.powers (algebraMap _ _ r))
      (by simp [Submonoid.powers_le]) = ⊤) :
    ZariskisMainProperty R p := by
  rw [zariskisMainProperty_iff] at h₁
  rw [zariskisMainProperty_iff']
  obtain ⟨s, hsp, hs, Hs⟩ := h₁
  obtain ⟨t, htp, Ht⟩ := h₂
  obtain ⟨m, hm⟩ := Hs t
  refine ⟨algebraMap _ _ (s ^ (m + 1) * t), ?_, fun x ↦ ?_⟩
  · simpa using ‹p.IsPrime›.mul_notMem
      (mt ((inferInstance : (p.under S).IsPrime).mem_of_pow_mem (m + 1)) hsp) htp
  obtain ⟨_, ⟨n, rfl⟩, a, ha⟩ := Ht.ge (Set.mem_univ x)
  obtain ⟨k, hk⟩ := Hs a
  refine ⟨k + n, ?_⟩
  convert_to IsIntegral R (algebraMap S T ((s ^ ((m + 1) * n) * (s ^ m * t) ^ k * (s ^ k * a))))
  · simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId] at ha
    simp only [map_pow, map_mul, ha, pow_add, mul_pow]
    ring
  · exact .algebraMap (.mul ((hs.pow _).mul (hm.pow _)) hk)

lemma ZariskisMainProperty.of_isIntegral (p : Ideal S) [p.IsPrime] [Algebra.IsIntegral R S] :
    ZariskisMainProperty R p :=
  zariskisMainProperty_iff'.mpr ⟨1, p.primeCompl.one_mem,
    fun _ ↦ ⟨0, Algebra.IsIntegral.isIntegral _⟩⟩

end Algebra

section IsStronglyTranscendental

variable (φ : R[X] →ₐ[R] S) (t : S) (p r : R[X])

lemma isIntegral_of_isIntegralElem_of_monic_of_natDegree_lt
    (ht : φ.IsIntegralElem t) (hpm : p.Monic)
    (hpr : r.natDegree < p.natDegree) (hp : φ p * t = φ r) : IsIntegral R t := by
  let St := Localization.Away t
  let t' : St := IsLocalization.Away.invSelf t
  have ht't : t' * algebraMap S St t = 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf]
  let R₁ := Algebra.adjoin R {t'}
  let R₂ := Algebra.adjoin R₁ {algebraMap S St (φ X)}
  letI : Algebra R₁ R₂ := R₂.algebra
  letI : Algebra R₂ St := R₂.toAlgebra
  letI : Algebra R₁ St := R₁.toAlgebra
  haveI : IsScalarTower R₁ R₂ St := Subalgebra.isScalarTower_mid _
  have : Algebra.IsIntegral R₁ R₂ := by
    cases subsingleton_or_nontrivial R₁
    · have := (algebraMap R₁ R₂).codomain_trivial; exact ⟨(Subsingleton.elim · 0 ▸ isIntegral_zero)⟩
    rw [← le_integralClosure_iff_isIntegral, Algebra.adjoin_le_iff, Set.singleton_subset_iff,
      SetLike.mem_coe, mem_integralClosure_iff]
    refine ⟨p.map (algebraMap R R₁) - C ⟨t', Algebra.self_mem_adjoin_singleton R t'⟩ *
        r.map (algebraMap R R₁), (hpm.map _).sub_of_left (degree_lt_degree ?_), ?_⟩
    · grw [natDegree_C_mul_le, natDegree_map_le, hpm.natDegree_map]; assumption
    · simp [← aeval_def, aeval_algebraMap_apply, aeval_algHom_apply,
        ← hp, ← mul_assoc, ht't, mul_right_comm]
  have : IsIntegral R₁ (algebraMap S St t) := by
    refine isIntegral_trans (A := R₂) (algebraMap S St t) ?_
    obtain ⟨q, hq, hq'⟩ := ht
    refine ⟨q.map (aeval ⟨_, Algebra.self_mem_adjoin_singleton _ _⟩).toRingHom, hq.map _, ?_⟩
    rw [AlgHom.toRingHom_eq_coe, eval₂_map, ← map_zero (algebraMap S St), ← hq',
      hom_eval₂]
    congr 1
    ext <;> simp [-Polynomial.algebraMap_apply, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simpa using IsLocalization.Away.isIntegral_of_isIntegral_map t
    (isIntegral_of_isIntegral_adjoin_of_mul_eq_one _ _ ht't this)
