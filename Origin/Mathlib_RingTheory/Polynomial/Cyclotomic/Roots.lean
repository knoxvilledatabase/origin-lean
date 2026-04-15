/-
Extracted from RingTheory/Polynomial/Cyclotomic/Roots.lean
Genuine: 12 of 19 | Dissolved: 7 | Infrastructure: 0
-/
import Origin.Core

/-!
# Roots of cyclotomic polynomials.

We gather results about roots of cyclotomic polynomials. In particular we show in
`Polynomial.cyclotomic_eq_minpoly` that `cyclotomic n R` is the minimal polynomial of a primitive
root of unity.

## Main results

* `IsPrimitiveRoot.isRoot_cyclotomic` : Any `n`-th primitive root of unity is a root of
  `cyclotomic n R`.
* `isRoot_cyclotomic_iff` : if `NeZero (n : R)`, then `μ` is a root of `cyclotomic n R`
  if and only if `μ` is a primitive root of unity.
* `Polynomial.cyclotomic_eq_minpoly` : `cyclotomic n ℤ` is the minimal polynomial of a primitive
  `n`-th root of unity `μ`.
* `Polynomial.cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

To prove `Polynomial.cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`Polynomial.cyclotomic_eq_minpoly` that `cyclotomic n ℤ` is the minimal polynomial of any `n`-th
primitive root of unity `μ : K`, where `K` is a field of characteristic `0`.
-/

namespace Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isRoot_of_unity_of_root_cyclotomic {ζ : R} {i : ℕ} (hi : i ∈ n.divisors)
    (h : (cyclotomic i R).IsRoot ζ) : ζ ^ n = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact pow_zero _
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm
  rw [eval_sub, eval_X_pow, eval_one] at this
  convert eq_add_of_sub_eq' this
  convert (add_zero (M := R) _).symm
  apply eval_eq_zero_of_dvd_of_eval_eq_zero _ h
  exact Finset.dvd_prod_of_mem _ hi

section IsDomain

variable [IsDomain R]

theorem _root_.isRoot_of_unity_iff (h : 0 < n) (R : Type*) [CommRing R] [IsDomain R] {ζ : R} :
    ζ ^ n = 1 ↔ ∃ i ∈ n.divisors, (cyclotomic i R).IsRoot ζ := by
  rw [← mem_nthRoots h, nthRoots, mem_roots <| X_pow_sub_C_ne_zero h _, C_1, ←
      prod_cyclotomic_eq_X_pow_sub_one h, isRoot_prod]

theorem _root_.IsPrimitiveRoot.isRoot_cyclotomic (hpos : 0 < n) {μ : R} (h : IsPrimitiveRoot μ n) :
    IsRoot (cyclotomic n R) μ := by
  rw [← mem_roots (cyclotomic_ne_zero n R), cyclotomic_eq_prod_X_sub_primitiveRoots h,
    roots_prod_X_sub_C, ← Finset.mem_def]
  rwa [← mem_primitiveRoots hpos] at h

-- DISSOLVED: isRoot_cyclotomic_iff'

-- DISSOLVED: isRoot_cyclotomic_iff

-- DISSOLVED: roots_cyclotomic_nodup

-- DISSOLVED: cyclotomic.roots_to_finset_eq_primitiveRoots

-- DISSOLVED: cyclotomic.roots_eq_primitiveRoots_val

-- DISSOLVED: isRoot_cyclotomic_iff_charZero

end IsDomain

theorem cyclotomic_injective [CharZero R] : Function.Injective fun n => cyclotomic n R := by
  intro n m hnm
  simp only at hnm
  rcases eq_or_ne n 0 with (rfl | hzero)
  · rw [cyclotomic_zero] at hnm
    replace hnm := congr_arg natDegree hnm
    rwa [natDegree_one, natDegree_cyclotomic, eq_comm, Nat.totient_eq_zero, eq_comm] at hnm
  · haveI := NeZero.mk hzero
    rw [← map_cyclotomic_int _ R, ← map_cyclotomic_int _ R] at hnm
    replace hnm := map_injective (Int.castRingHom R) Int.cast_injective hnm
    replace hnm := congr_arg (map (Int.castRingHom ℂ)) hnm
    rw [map_cyclotomic_int, map_cyclotomic_int] at hnm
    have hprim := Complex.isPrimitiveRoot_exp _ hzero
    have hroot := isRoot_cyclotomic_iff (R := ℂ).2 hprim
    rw [hnm] at hroot
    haveI hmzero : NeZero m := ⟨fun h => by simp [h] at hroot⟩
    rw [isRoot_cyclotomic_iff (R := ℂ)] at hroot
    replace hprim := hprim.eq_orderOf
    rwa [← IsPrimitiveRoot.eq_orderOf hroot] at hprim

theorem _root_.IsPrimitiveRoot.minpoly_dvd_cyclotomic {n : ℕ} {K : Type*} [Field K] {μ : K}
    (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : minpoly ℤ μ ∣ cyclotomic n ℤ := by
  apply minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos)
  simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def] using h.isRoot_cyclotomic hpos

section minpoly

open IsPrimitiveRoot Complex

-- DISSOLVED: _root_.IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible

theorem cyclotomic_eq_minpoly {n : ℕ} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : cyclotomic n ℤ = minpoly ℤ μ := by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsPrimitiveRoot.isIntegral h hpos))
    (cyclotomic.monic n ℤ) (h.minpoly_dvd_cyclotomic hpos) ?_
  simpa [natDegree_cyclotomic n ℤ] using totient_le_degree_minpoly h

theorem cyclotomic_eq_minpoly_rat {n : ℕ} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : cyclotomic n ℚ = minpoly ℚ μ := by
  rw [← map_cyclotomic_int, cyclotomic_eq_minpoly h hpos]
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' _ (IsPrimitiveRoot.isIntegral h hpos)).symm

theorem cyclotomic.irreducible {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℤ) := by
  rw [cyclotomic_eq_minpoly (isPrimitiveRoot_exp n hpos.ne') hpos]
  apply minpoly.irreducible
  exact (isPrimitiveRoot_exp n hpos.ne').isIntegral hpos

theorem cyclotomic.irreducible_rat {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℚ) := by
  rw [← map_cyclotomic_int]
  exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map (cyclotomic.isPrimitive n ℤ)).1
    (cyclotomic.irreducible hpos)

theorem cyclotomic.isCoprime_rat {n m : ℕ} (h : n ≠ m) :
    IsCoprime (cyclotomic n ℚ) (cyclotomic m ℚ) := by
  rcases n.eq_zero_or_pos with (rfl | hnzero)
  · exact isCoprime_one_left
  rcases m.eq_zero_or_pos with (rfl | hmzero)
  · exact isCoprime_one_right
  rw [Irreducible.coprime_iff_not_dvd <| cyclotomic.irreducible_rat <| hnzero]
  exact fun hdiv => h <| cyclotomic_injective <|
    eq_of_monic_of_associated (cyclotomic.monic n ℚ) (cyclotomic.monic m ℚ) <|
      Irreducible.associated_of_dvd (cyclotomic.irreducible_rat hnzero)
        (cyclotomic.irreducible_rat hmzero) hdiv

end minpoly

end Polynomial

namespace IsPrimitiveRoot

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

variable {p : ℕ} {ζ : K}

lemma sum_eq_zero_iff_forall_eq (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α : Fin p → ℚ) :
    ∑ i, α i * ζ ^ i.val = 0 ↔ ∀ i j, α i = α j := by
  haveI : Fact p.Prime := ⟨hp⟩
  let P : ℚ[X] := ∑ i, C (α i) * X ^ i.1
  have hP (i : Fin p) : α i = P.coeff i := by simp [P, ← Fin.ext_iff]
  have hP' : P.degree ≤ ↑(p - 1) :=
    (degree_sum_le ..).trans (Finset.sup_le fun _ _ ↦ by grw [degree_C_mul_X_pow_le]; simp; grind)
  trans aeval ζ P = 0; · simp [P]
  rw [← minpoly.dvd_iff, ← cyclotomic_eq_minpoly_rat hζ hp.pos]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun H ↦ ⟨C (α 0), Polynomial.ext fun i ↦ if h : i < p then ?_ else ?_⟩⟩
  · rw [hc, degree_mul, degree_cyclotomic, Nat.totient_prime hp] at hP'
    have : c.degree ≤ 0 := (WithBot.add_le_add_iff_left (x := ↑(p - 1)) (by simp)).mp (by simpa)
    obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp (natDegree_eq_zero_iff_degree_le_zero.mpr this)
    simp [hP, hc, cyclotomic_prime]
  · lift i to Fin p using h; simp [cyclotomic_prime, ← hP, H i 0]
  · simp [cyclotomic_prime, P, h, Fin.forall_iff, @forall_comm _ (_ = _), Finset.sum_eq_zero]

lemma sum_eq_zero_iff_forall_eq_int (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α : Fin p → ℤ) :
    ∑ i, α i * ζ ^ i.val = 0 ↔ ∀ i j, α i = α j := by
  simpa using sum_eq_zero_iff_forall_eq hp hζ (Int.cast ∘ α)

end IsPrimitiveRoot
