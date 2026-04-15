/-
Extracted from RingTheory/NoetherNormalization.lean
Genuine: 12 of 16 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core

/-!
# Noether normalization lemma
This file contains a proof by Nagata of the Noether normalization lemma.

## Main Results
Let `A` be a finitely generated algebra over a field `k`.
Then there exists a natural number `s` and an injective homomorphism
from `k[X_0, X_1, ..., X_(s-1)]` to `A` such that `A` is integral over `k[X_0, X_1, ..., X_(s-1)]`.

## Strategy of the proof
Suppose `f` is a nonzero polynomial in `n+1` variables.
First, we construct an algebra equivalence `T` from `k[X_0,...,X_n]` to itself such that
`f` is mapped to a polynomial in `X_0` with invertible leading coefficient.
More precisely, `T` maps `X_i` to `X_i + X_0 ^ r_i` when `i ≠ 0`, and `X_0` to `X_0`.
Here we choose `r_i` to be `up ^ i` where `up` is big enough, so that `T` maps
different monomials of `f` to polynomials with different degrees in `X_0`.
See `degreeOf_t_ne_of_ne`.

Secondly, we construct the following maps: let `I` be an ideal containing `f` and
let `φ : k[X_0,...X_{n-1}] ≃ₐ[k] k[X_1,...X_n][X]` be the natural isomorphism.

- `hom1 : k[X_0,...X_{n-1}] →ₐ[k[X_0,...X_{n-1}]] k[X_1,...X_n][X]/φ(T(I))`
- `eqv1 : k[X_1,...X_n][X]/φ(T(I)) ≃ₐ[k] k[X_0,...,X_n]/T(I)`
- `eqv2 : k[X_0,...,X_n]/T(I) ≃ₐ[k] k[X_0,...,X_n]/I`
- `hom2 : k[X_0,...X_(n-1)] →ₐ[k] k[X_0,...X_n]/I`

`hom1` is integral because `φ(T(I))` contains a monic polynomial. See `hom1_isIntegral`.
`hom2` is integral because it's the composition of integral maps. See `hom2_isIntegral`.

Finally We use induction to prove there is an injective map from `k[X_0,...,X_{s-1}]`
to `k[X_0,...,X_(n-1)]/I`.The case `n=0` is trivial.
For `n+1`, if `I = 0` there is nothing to do.
Otherwise, `hom2` induces a map `φ` by quotient kernel.
We use the inductive hypothesis on k[X_1,...,X_n] and the kernel of `hom2` to get `s, g`.
Composing `φ` and `g` we get the desired map since both `φ` and `g` are injective and integral.

## Reference
* <https://stacks.math.columbia.edu/tag/00OW>

## TODO
* In the final theorems, consider setting `s` equal to the Krull dimension of `R`.
-/

open Polynomial MvPolynomial Ideal Nat RingHom List

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)

variable (v w : Fin (n + 1) →₀ ℕ)

namespace NoetherNormalization

section equivT

local notation3 "up" => 2 + f.totalDegree

variable {f v} in

private lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

private lemma t1_comp_t1_neg (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

private noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))

private lemma sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using h

-- DISSOLVED: degreeOf_zero_t

private lemma degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv, degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

private lemma leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

-- DISSOLVED: T_leadingcoeff_isUnit

end equivT

section intmaps

variable (I : Ideal (MvPolynomial (Fin (n + 1)) k))

private noncomputable abbrev hom1 : MvPolynomial (Fin n) k →ₐ[MvPolynomial (Fin n) k]
    (MvPolynomial (Fin n) k)[X] ⧸ (I.map <| T f).map (finSuccEquiv k n) :=
  (Quotient.mkₐ (MvPolynomial (Fin n) k) (map (finSuccEquiv k n) (map (T f) I))).comp
  (Algebra.ofId (MvPolynomial (Fin n) k) ((MvPolynomial (Fin n) k)[X]))

-- DISSOLVED: hom1_isIntegral

private noncomputable abbrev eqv1 :
    ((MvPolynomial (Fin n) k)[X] ⧸ (I.map (T f)).map (finSuccEquiv k n)) ≃ₐ[k]
    MvPolynomial (Fin (n + 1)) k ⧸ I.map (T f) := quotientEquivAlg
  ((I.map (T f)).map (finSuccEquiv k n)) (I.map (T f)) (finSuccEquiv k n).symm <| by
  set g := (finSuccEquiv k n)
  have : g.symm.toRingEquiv.toRingHom.comp g = RingHom.id _ :=
    g.toRingEquiv.symm_toRingHom_comp_toRingHom
  calc
    _ = Ideal.map ((RingHom.id _).comp <| T f) I := by rw [id_comp, Ideal.map_coe]
    _ = (I.map (T f)).map (RingHom.id _) := by simp only [← Ideal.map_map, Ideal.map_coe]
    _ = (I.map (T f)).map (g.symm.toAlgHom.toRingHom.comp g) :=
      congrFun (congrArg Ideal.map this.symm) (I.map (T f))
    _ = _ := by simp [← Ideal.map_map, Ideal.map_coe]

private noncomputable abbrev eqv2 :
    (MvPolynomial (Fin (n + 1)) k ⧸ I.map (T f)) ≃ₐ[k] MvPolynomial (Fin (n + 1)) k ⧸ I :=
  quotientEquivAlg (R₁ := k) (I.map (T f)) I (T f).symm <| by
  calc
    _ = I.map ((T f).symm.toRingEquiv.toRingHom.comp (T f)) := by
      have : (T f).symm.toRingEquiv.toRingHom.comp (T f) = RingHom.id _ :=
        RingEquiv.symm_toRingHom_comp_toRingHom _
      rw [this, Ideal.map_id]
    _ = _ := by
      rw [← Ideal.map_map, Ideal.map_coe, Ideal.map_coe]
      exact congrArg _ rfl

private noncomputable def hom2 : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k ⧸ I :=
  (eqv2 f I).toAlgHom.comp ((eqv1 f I).toAlgHom.comp ((hom1 f I).restrictScalars k))

-- DISSOLVED: hom2_isIntegral

end intmaps

end NoetherNormalization

section mainthm

open NoetherNormalization

theorem exists_integral_inj_algHom_of_quotient (I : Ideal (MvPolynomial (Fin n) k))
    (hi : I ≠ ⊤) : ∃ s ≤ n, ∃ g : (MvPolynomial (Fin s) k) →ₐ[k] ((MvPolynomial (Fin n) k) ⧸ I),
    Function.Injective g ∧ g.IsIntegral := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, Quotient.mkₐ k I, fun a b hab ↦ ?_,
      isIntegral_of_surjective _ (Quotient.mkₐ_surjective k I)⟩
    rw [Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hab
    by_contra ne
    have eq := eq_C_of_isEmpty (a - b)
    have ne : coeff 0 (a - b) ≠ 0 := fun h ↦ h ▸ eq ▸ sub_ne_zero_of_ne ne <| map_zero _
    obtain ⟨c, _, eqr⟩ := isUnit_iff_exists.mp ne.isUnit
    have one : c • (a - b) = 1 := by
      rw [MvPolynomial.smul_eq_C_mul, eq, ← map_mul, eqr, MvPolynomial.C_1]
    exact hi ((eq_top_iff_one I).mpr (one ▸ I.smul_of_tower_mem c hab))
  | succ d hd =>
    by_cases eqi : I = 0
    · have bij : Function.Bijective (Quotient.mkₐ k I) :=
        (Quotient.mk_bijective_iff_eq_bot I).mpr eqi
      exact ⟨d + 1, le_rfl, _, bij.1, isIntegral_of_surjective _ bij.2⟩
    · obtain ⟨f, fi, fne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot eqi
      set ϕ := kerLiftAlg <| hom2 f I
      have := Quotient.nontrivial_iff.mpr hi
      obtain ⟨s, _, g, injg, intg⟩ := hd (ker <| hom2 f I) (ker_ne_top <| hom2 f I)
      have comp : (kerLiftAlg (hom2 f I)).comp (Quotient.mkₐ k <| ker <| hom2 f I) = (hom2 f I) :=
        AlgHom.ext fun a ↦ by
          simp only [AlgHom.coe_comp, Quotient.mkₐ_eq_mk, Function.comp_apply, kerLiftAlg_mk]
      exact ⟨s, by lia, ϕ.comp g, (ϕ.coe_comp  g) ▸ (kerLiftAlg_injective _).comp injg,
        intg.trans _ _ <| (comp ▸ hom2_isIntegral f I fne fi).tower_top _ _⟩

variable (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [a : Algebra k R]
  [fin : Algebra.FiniteType k R]
