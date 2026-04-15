/-
Extracted from RingTheory/Ideal/GoingUp.lean
Genuine: 31 of 42 | Dissolved: 8 | Infrastructure: 3
-/
import Origin.Core

/-!
# Ideals over/under ideals in integral extensions

This file proves some going-up results for integral algebras.

## Implementation notes

The proofs of the `comap_ne_bot` and `comap_lt_comap` families use an approach
specific for their situation: we construct an element in `I.comap f` from the
coefficients of a minimal polynomial.
Once mathlib has more material on the localization at a prime ideal, the results
can be proven using more general going-up/going-down theory.
-/

open Polynomial Submodule

open scoped Pointwise

namespace Ideal

variable {R : Type*} [CommRing R]

variable {S : Type*} [CommRing S] {f : R →+* S} {I J : Ideal S}

theorem coeff_zero_mem_comap_of_root_mem_of_eval_mem {r : S} (hr : r ∈ I) {p : R[X]}
    (hp : p.eval₂ f r ∈ I) : p.coeff 0 ∈ I.comap f := by
  rw [← p.divX_mul_X_add, eval₂_add, eval₂_C, eval₂_mul, eval₂_X] at hp
  refine mem_comap.mpr ((I.add_mem_iff_right ?_).mp hp)
  exact I.mul_mem_left _ hr

theorem coeff_zero_mem_comap_of_root_mem {r : S} (hr : r ∈ I) {p : R[X]} (hp : p.eval₂ f r = 0) :
    p.coeff 0 ∈ I.comap f :=
  coeff_zero_mem_comap_of_root_mem_of_eval_mem hr (hp.symm ▸ I.zero_mem)

-- DISSOLVED: exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem

theorem injective_quotient_le_comap_map (P : Ideal R[X]) :
    Function.Injective <|
      Ideal.quotientMap
        (Ideal.map (Polynomial.mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) P)
        (Polynomial.mapRingHom (Ideal.Quotient.mk (P.comap (C : R →+* R[X]))))
        le_comap_map := by
  refine quotientMap_injective' (le_of_eq ?_)
  rw [comap_map_of_surjective (mapRingHom (Ideal.Quotient.mk (P.comap (C : R →+* R[X]))))
      (map_surjective (Ideal.Quotient.mk (P.comap (C : R →+* R[X]))) Ideal.Quotient.mk_surjective)]
  refine le_antisymm (sup_le le_rfl ?_) (le_sup_of_le_left le_rfl)
  refine fun p hp =>
    polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => Ideal.Quotient.eq_zero_iff_mem.mp ?_
  simpa only [coeff_map, coe_mapRingHom] using ext_iff.mp (Ideal.mem_bot.mp (mem_comap.mp hp)) n

theorem quotient_mk_maps_eq (P : Ideal R[X]) :
    ((Quotient.mk (map (mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) P)).comp C).comp
        (Quotient.mk (P.comap (C : R →+* R[X]))) =
      (Ideal.quotientMap (map (mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) P)
            (mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) le_comap_map).comp
        ((Quotient.mk P).comp C) := by
  ext
  simp

-- DISSOLVED: exists_nonzero_mem_of_ne_bot

end

section IsDomain

variable {R : Type*} [CommRing R]

variable {S : Type*} [CommRing S] {f : R →+* S} {I J : Ideal S}

-- DISSOLVED: exists_coeff_ne_zero_mem_comap_of_root_mem

-- DISSOLVED: exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff

-- DISSOLVED: comap_lt_comap_of_root_mem_sdiff

theorem mem_of_one_mem (h : (1 : S) ∈ I) (x) : x ∈ I :=
  (I.eq_top_iff_one.mpr h).symm ▸ mem_top

theorem comap_lt_comap_of_integral_mem_sdiff [Algebra R S] [hI : I.IsPrime] (hIJ : I ≤ J) {x : S}
    (mem : x ∈ (J : Set S) \ I) (integral : IsIntegral R x) :
    I.comap (algebraMap R S) < J.comap (algebraMap R S) := by
  obtain ⟨p, p_monic, hpx⟩ := integral
  refine comap_lt_comap_of_root_mem_sdiff hIJ mem (map_monic_ne_zero p_monic) ?_
  convert I.zero_mem

-- DISSOLVED: comap_ne_bot_of_root_mem

theorem isMaximal_of_isIntegral_of_isMaximal_comap [Algebra R S] [Algebra.IsIntegral R S]
    (I : Ideal S) [I.IsPrime] (hI : IsMaximal (I.comap (algebraMap R S))) : IsMaximal I :=
  ⟨⟨mt comap_eq_top_iff.mpr hI.1.1, fun _ I_lt_J =>
      let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
      comap_eq_top_iff.1 <|
        hI.1.2 _ (comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩
          (Algebra.IsIntegral.isIntegral x))⟩⟩

theorem isMaximal_of_isIntegral_of_isMaximal_comap' (f : R →+* S) (hf : f.IsIntegral) (I : Ideal S)
    [I.IsPrime] (hI : IsMaximal (I.comap f)) : IsMaximal I :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_of_isIntegral_of_isMaximal_comap (R := R) (S := S) I hI

variable [Algebra R S]

-- DISSOLVED: comap_ne_bot_of_algebraic_mem

-- DISSOLVED: comap_ne_bot_of_integral_mem

theorem eq_bot_of_comap_eq_bot [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
    (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  by_cases hx0 : x = 0
  · exact hx0.symm ▸ Ideal.zero_mem ⊥
  · exact absurd hI (comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x))

theorem isMaximal_comap_of_isIntegral_of_isMaximal [Algebra.IsIntegral R S] (I : Ideal S)
    [hI : I.IsMaximal] : IsMaximal (I.comap (algebraMap R S)) := by
  refine Ideal.Quotient.maximal_of_isField _ ?_
  haveI : IsPrime (I.comap (algebraMap R S)) := comap_isPrime _ _
  exact isField_of_isIntegral_of_isField
    algebraMap_quotient_injective (by rwa [← Quotient.maximal_ideal_iff_isField_quotient])

theorem isMaximal_comap_of_isIntegral_of_isMaximal' {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (I : Ideal S) [I.IsMaximal] : IsMaximal (I.comap f) :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := S) I

section IsIntegralClosure

variable (S) {A : Type*} [CommRing A]

variable [Algebra R A] [Algebra A S] [IsScalarTower R A S] [IsIntegralClosure A R S]

include S

theorem IsIntegralClosure.comap_lt_comap {I J : Ideal A} [I.IsPrime] (I_lt_J : I < J) :
    I.comap (algebraMap R A) < J.comap (algebraMap R A) :=
  let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
  comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (IsIntegralClosure.isIntegral R S x)

theorem IsIntegralClosure.isMaximal_of_isMaximal_comap (I : Ideal A) [I.IsPrime]
    (hI : IsMaximal (I.comap (algebraMap R A))) : IsMaximal I :=
  have : Algebra.IsIntegral R A := IsIntegralClosure.isIntegral_algebra R S
  isMaximal_of_isIntegral_of_isMaximal_comap I hI

variable [IsDomain A]

theorem IsIntegralClosure.comap_ne_bot [Nontrivial R] {I : Ideal A} (I_ne_bot : I ≠ ⊥) :
    I.comap (algebraMap R A) ≠ ⊥ :=
  let ⟨x, x_mem, x_ne_zero⟩ := I.ne_bot_iff.mp I_ne_bot
  comap_ne_bot_of_integral_mem x_ne_zero x_mem (IsIntegralClosure.isIntegral R S x)

theorem IsIntegralClosure.eq_bot_of_comap_eq_bot [Nontrivial R] {I : Ideal A} :
    I.comap (algebraMap R A) = ⊥ → I = ⊥ := by
  contrapose
  exact IsIntegralClosure.comap_ne_bot S

end IsIntegralClosure

theorem IntegralClosure.comap_lt_comap {I J : Ideal (integralClosure R S)} [I.IsPrime]
    (I_lt_J : I < J) :
    I.comap (algebraMap R (integralClosure R S)) < J.comap (algebraMap R (integralClosure R S)) :=
  IsIntegralClosure.comap_lt_comap S I_lt_J

theorem IntegralClosure.isMaximal_of_isMaximal_comap (I : Ideal (integralClosure R S)) [I.IsPrime]
    (hI : IsMaximal (I.comap (algebraMap R (integralClosure R S)))) : IsMaximal I :=
  IsIntegralClosure.isMaximal_of_isMaximal_comap S I hI

variable [IsDomain S]

theorem IntegralClosure.comap_ne_bot [Nontrivial R] {I : Ideal (integralClosure R S)}
    (I_ne_bot : I ≠ ⊥) : I.comap (algebraMap R (integralClosure R S)) ≠ ⊥ :=
  IsIntegralClosure.comap_ne_bot S I_ne_bot

theorem IntegralClosure.eq_bot_of_comap_eq_bot [Nontrivial R] {I : Ideal (integralClosure R S)} :
    I.comap (algebraMap R (integralClosure R S)) = ⊥ → I = ⊥ :=
  IsIntegralClosure.eq_bot_of_comap_eq_bot S

theorem exists_ideal_over_prime_of_isIntegral_of_isDomain [Algebra.IsIntegral R S] (P : Ideal R)
    [IsPrime P] (hP : RingHom.ker (algebraMap R S) ≤ P) :
    ∃ Q : Ideal S, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  have hP0 : (0 : S) ∉ Algebra.algebraMapSubmonoid S P.primeCompl := by
    rintro ⟨x, ⟨hx, x0⟩⟩
    exact absurd (hP x0) hx
  let Rₚ := Localization P.primeCompl
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  letI : IsDomain (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors hP0)
  obtain ⟨Qₚ : Ideal Sₚ, Qₚ_maximal⟩ := exists_maximal Sₚ
  let _ : Algebra Rₚ Sₚ := localizationAlgebra P.primeCompl S
  have : Algebra.IsIntegral Rₚ Sₚ := ⟨isIntegral_localization⟩
  have Qₚ_max : IsMaximal (comap _ Qₚ) :=
    isMaximal_comap_of_isIntegral_of_isMaximal (R := Rₚ) (S := Sₚ) Qₚ
  refine ⟨comap (algebraMap S Sₚ) Qₚ, ⟨comap_isPrime _ Qₚ, ?_⟩⟩
  convert Localization.AtPrime.comap_maximalIdeal (I := P)
  rw [comap_comap, ← IsLocalRing.eq_maximalIdeal Qₚ_max,
    ← IsLocalization.map_comp (P := S) (Q := Sₚ) (g := algebraMap R S)
    (M := P.primeCompl) (T := Algebra.algebraMapSubmonoid S P.primeCompl) (S := Rₚ)
    (fun p hp => Algebra.mem_algebraMapSubmonoid_of_mem ⟨p, hp⟩)]
  rfl

end

theorem exists_ideal_over_prime_of_isIntegral_of_isPrime
    [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P]
    (I : Ideal S) [IsPrime I] (hIP : I.comap (algebraMap R S) ≤ P) :
    ∃ Q ≥ I, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  obtain ⟨Q' : Ideal (S ⧸ I), ⟨Q'_prime, hQ'⟩⟩ :=
    @exists_ideal_over_prime_of_isIntegral_of_isDomain (R ⧸ I.comap (algebraMap R S)) _ (S ⧸ I) _
      Ideal.quotientAlgebra _ _
      (map (Ideal.Quotient.mk (I.comap (algebraMap R S))) P)
      (map_isPrime_of_surjective Quotient.mk_surjective (by simp [hIP]))
      (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot _).1 algebraMap_quotient_injective))
        bot_le)
  refine ⟨Q'.comap _, le_trans (le_of_eq mk_ker.symm) (ker_le_comap _), ⟨comap_isPrime _ Q', ?_⟩⟩
  rw [comap_comap]
  refine _root_.trans ?_ (_root_.trans (congr_arg (comap (Ideal.Quotient.mk
    (comap (algebraMap R S) I))) hQ') ?_)
  · rw [comap_comap]
    exact congr_arg (comap · Q') (RingHom.ext fun r => rfl)
  · refine _root_.trans (comap_map_of_surjective _ Quotient.mk_surjective _) (sup_eq_left.2 ?_)
    simpa [← RingHom.ker_eq_comap_bot] using hIP

theorem exists_ideal_over_prime_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P]
    (I : Ideal S) (hIP : I.comap (algebraMap R S) ≤ P) :
    ∃ Q ≥ I, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  have ⟨P', hP, hP', hP''⟩ := exists_ideal_comap_le_prime P I hIP
  obtain ⟨Q, hQ, hQ', hQ''⟩ := exists_ideal_over_prime_of_isIntegral_of_isPrime P P' hP''
  exact ⟨Q, hP.trans hQ, hQ', hQ''⟩

-- INSTANCE (free from Core): nonempty_primesOver

theorem exists_ideal_over_maximal_of_isIntegral [Algebra.IsIntegral R S]
    (P : Ideal R) [P_max : IsMaximal P] (hP : RingHom.ker (algebraMap R S) ≤ P) :
    ∃ Q : Ideal S, IsMaximal Q ∧ Q.comap (algebraMap R S) = P := by
  obtain ⟨Q, -, Q_prime, hQ⟩ := exists_ideal_over_prime_of_isIntegral P ⊥ hP
  exact ⟨Q, isMaximal_of_isIntegral_of_isMaximal_comap _ (hQ.symm ▸ P_max), hQ⟩

theorem exists_maximal_ideal_liesOver_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (P : Ideal R) [P.IsMaximal] :
    ∃ (Q : Ideal S), Q.IsMaximal ∧ Q.LiesOver P := by
  simp_rw [liesOver_iff, eq_comm (a := P)]
  exact exists_ideal_over_maximal_of_isIntegral P (by
    simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)])

lemma map_eq_top_iff_of_ker_le {R S} [CommRing R] [CommRing S]
    (f : R →+* S) {I : Ideal R} (hf₁ : RingHom.ker f ≤ I) (hf₂ : f.IsIntegral) :
    I.map f = ⊤ ↔ I = ⊤ := by
  constructor; swap
  · rintro rfl; exact Ideal.map_top _
  contrapose
  intro h
  obtain ⟨m, _, hm⟩ := Ideal.exists_le_maximal I h
  let _ := f.toAlgebra
  have : Algebra.IsIntegral _ _ := ⟨hf₂⟩
  obtain ⟨m', _, rfl⟩ := exists_ideal_over_maximal_of_isIntegral m (hf₁.trans hm)
  rw [← map_le_iff_le_comap] at hm
  exact (hm.trans_lt (lt_top_iff_ne_top.mpr (IsMaximal.ne_top ‹_›))).ne

lemma map_eq_top_iff {R S} [CommRing R] [CommRing S]
    (f : R →+* S) {I : Ideal R} (hf₁ : Function.Injective f) (hf₂ : f.IsIntegral) :
    I.map f = ⊤ ↔ I = ⊤ :=
  map_eq_top_iff_of_ker_le f (by simp [(RingHom.injective_iff_ker_eq_bot f).mp hf₁]) hf₂

lemma exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton
    {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] (hq : p.primesOver S = {q})
    [Algebra.IsIntegral R S] (x : S) (hx : x ∉ q) : ∃ r ∉ p, x ∣ algebraMap _ _ r := by
  simp only [dvd_def, eq_comm, mul_comm x]
  by_contra!
  obtain ⟨Q, hQ, hxQ, hQp⟩ := Ideal.exists_le_prime_disjoint (.span {x})
    (Algebra.algebraMapSubmonoid _ p.primeCompl)
    (by simpa [Set.disjoint_iff_forall_ne, Ideal.mem_span_singleton',
      Algebra.algebraMapSubmonoid, @forall_comm S])
  have hQp' : Q.under _ ≤ p := by
    intro x hxQ
    by_contra hxp
    exact Set.subset_compl_iff_disjoint_right.mpr hQp hxQ ⟨x, hxp, rfl⟩
  obtain ⟨Q', hQ'Q, hQ', hQ'p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime _ _ hQp'
  obtain rfl : Q' = q := hq.le ⟨hQ', ⟨hQ'p.symm⟩⟩
  exact hx (hQ'Q (hxQ (Ideal.mem_span_singleton_self _)))

end IsDomain

section IsIntegral

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
  (P : Ideal B) (p : Ideal A) [P.LiesOver p]

variable (A) in

-- INSTANCE (free from Core): IsMaximal.under

theorem IsMaximal.of_liesOver_isMaximal [hpm : p.IsMaximal] [P.IsPrime] : P.IsMaximal := by
  rw [P.over_def p] at hpm
  exact isMaximal_of_isIntegral_of_isMaximal_comap P hpm

theorem IsMaximal.of_isMaximal_liesOver [P.IsMaximal] : p.IsMaximal := by
  rw [P.over_def p]
  exact isMaximal_comap_of_isIntegral_of_isMaximal P

variable (A) in

theorem eq_bot_of_liesOver_bot [Nontrivial A] [IsDomain B] [h : P.LiesOver (⊥ : Ideal A)] :
    P = ⊥ :=
  eq_bot_of_comap_eq_bot <| ((liesOver_iff _ _).mp h).symm

variable (A) {P} in

theorem under_ne_bot [Nontrivial A] [IsDomain B] (hP : P ≠ ⊥) : under A P ≠ ⊥ :=
  fun h ↦ hP <| eq_bot_of_comap_eq_bot h

-- INSTANCE (free from Core): Quotient.algebra_isIntegral_of_liesOver
