/-
Extracted from Algebra/Polynomial/FieldDivision.lean
Genuine: 49 of 87 | Dissolved: 32 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.EuclideanDomain

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $R[X]$

-/

noncomputable section

open Polynomial

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R]

-- DISSOLVED: rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero

theorem derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} (hpt : Polynomial.IsRoot p t)
    (hnzd : (p.rootMultiplicity t : R) ∈ nonZeroDivisors R) :
    (derivative p).rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · simp only [h, map_zero, rootMultiplicity_zero]
  obtain ⟨g, hp, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h t
  set m := p.rootMultiplicity t
  have hm : m - 1 + 1 = m := Nat.sub_add_cancel <| (rootMultiplicity_pos h).2 hpt
  have hndvd : ¬(X - C t) ^ m ∣ derivative p := by
    rw [hp, derivative_mul, dvd_add_left (dvd_mul_right _ _),
      derivative_X_sub_C_pow, ← hm, pow_succ, hm, mul_comm (C _), mul_assoc,
      dvd_cancel_left_mem_nonZeroDivisors (monic_X_sub_C t |>.pow _ |>.mem_nonZeroDivisors)]
    rw [dvd_iff_isRoot, IsRoot] at hndvd ⊢
    rwa [eval_mul, eval_C, mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd]
  have hnezero : derivative p ≠ 0 := fun h ↦ hndvd (by rw [h]; exact dvd_zero _)
  exact le_antisymm (by rwa [rootMultiplicity_le_iff hnezero, hm])
    (rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero _ t hnezero)

theorem isRoot_iterate_derivative_of_lt_rootMultiplicity {p : R[X]} {t : R} {n : ℕ}
    (hn : n < p.rootMultiplicity t) : (derivative^[n] p).IsRoot t :=
  dvd_iff_isRoot.mp <| (dvd_pow_self _ <| Nat.sub_ne_zero_of_lt hn).trans
    (pow_sub_dvd_iterate_derivative_of_pow_dvd _ <| p.pow_rootMultiplicity_dvd t)

open Finset in

theorem eval_iterate_derivative_rootMultiplicity {p : R[X]} {t : R} :
    (derivative^[p.rootMultiplicity t] p).eval t =
      (p.rootMultiplicity t).factorial • (p /ₘ (X - C t) ^ p.rootMultiplicity t).eval t := by
  set m := p.rootMultiplicity t with hm
  conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq t, ← hm]
  rw [iterate_derivative_mul, eval_finset_sum, sum_eq_single_of_mem _ (mem_range.mpr m.succ_pos)]
  · rw [m.choose_zero_right, one_smul, eval_mul, m.sub_zero, iterate_derivative_X_sub_pow_self,
      eval_natCast, nsmul_eq_mul]; rfl
  · intro b hb hb0
    rw [iterate_derivative_X_sub_pow, eval_smul, eval_mul, eval_smul, eval_pow,
      Nat.sub_sub_self (mem_range_succ_iff.mp hb), eval_sub, eval_X, eval_C, sub_self,
      zero_pow hb0, smul_zero, zero_mul, smul_zero]

-- DISSOLVED: lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors

-- DISSOLVED: lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'

-- DISSOLVED: lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors

-- DISSOLVED: lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'

-- DISSOLVED: one_lt_rootMultiplicity_iff_isRoot_iterate_derivative

-- DISSOLVED: one_lt_rootMultiplicity_iff_isRoot

end CommRing

section IsDomain

variable [CommRing R] [IsDomain R]

-- DISSOLVED: one_lt_rootMultiplicity_iff_isRoot_gcd

theorem derivative_rootMultiplicity_of_root [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t) :
    p.derivative.rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · rw [h, map_zero, rootMultiplicity_zero]
  exact derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hpt <|
    mem_nonZeroDivisors_of_ne_zero <| Nat.cast_ne_zero.2 ((rootMultiplicity_pos h).2 hpt).ne'

theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity [CharZero R] (p : R[X]) (t : R) :
    p.rootMultiplicity t - 1 ≤ p.derivative.rootMultiplicity t := by
  by_cases h : p.IsRoot t
  · exact (derivative_rootMultiplicity_of_root h).symm.le
  · rw [rootMultiplicity_eq_zero h, zero_tsub]
    exact zero_le _

-- DISSOLVED: lt_rootMultiplicity_of_isRoot_iterate_derivative

-- DISSOLVED: lt_rootMultiplicity_iff_isRoot_iterate_derivative

-- DISSOLVED: isRoot_of_isRoot_of_dvd_derivative_mul

section NormalizationMonoid

variable [NormalizationMonoid R]

instance instNormalizationMonoid : NormalizationMonoid R[X] where
  normUnit p :=
    ⟨C ↑(normUnit p.leadingCoeff), C ↑(normUnit p.leadingCoeff)⁻¹, by
      rw [← RingHom.map_mul, Units.mul_inv, C_1], by rw [← RingHom.map_mul, Units.inv_mul, C_1]⟩
  normUnit_zero := Units.ext (by simp)
  normUnit_mul hp0 hq0 :=
    Units.ext
      (by
        dsimp
        rw [Ne, ← leadingCoeff_eq_zero] at *
        rw [leadingCoeff_mul, normUnit_mul hp0 hq0, Units.val_mul, C_mul])
  normUnit_coe_units u :=
    Units.ext
      (by
        dsimp
        rw [← mul_one u⁻¹, Units.val_mul, Units.eq_inv_mul_iff_mul_eq]
        rcases Polynomial.isUnit_iff.1 ⟨u, rfl⟩ with ⟨_, ⟨w, rfl⟩, h2⟩
        rw [← h2, leadingCoeff_C, normUnit_coe_units, ← C_mul, Units.mul_inv, C_1]
        rfl)

@[simp]
theorem coe_normUnit {p : R[X]} : (normUnit p : R[X]) = C ↑(normUnit p.leadingCoeff) := by
  simp [normUnit]

@[simp]
theorem leadingCoeff_normalize (p : R[X]) :
    leadingCoeff (normalize p) = normalize (leadingCoeff p) := by simp [normalize_apply]

theorem Monic.normalize_eq_self {p : R[X]} (hp : p.Monic) : normalize p = p := by
  simp only [Polynomial.coe_normUnit, normalize_apply, hp.leadingCoeff, normUnit_one,
    Units.val_one, Polynomial.C.map_one, mul_one]

alias normalize_monic := Monic.normalize_eq_self

theorem roots_normalize {p : R[X]} : (normalize p).roots = p.roots := by
  rw [normalize_apply, mul_comm, coe_normUnit, roots_C_mul _ (normUnit (leadingCoeff p)).ne_zero]

theorem normUnit_X : normUnit (X : Polynomial R) = 1 := by
  have := coe_normUnit (R := R) (p := X)
  rwa [leadingCoeff_X, normUnit_one, Units.val_one, map_one, Units.val_eq_one] at this

theorem X_eq_normalize : (X : Polynomial R) = normalize X := by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

end NormalizationMonoid

end IsDomain

section DivisionRing

variable [DivisionRing R] {p q : R[X]}

-- DISSOLVED: degree_pos_of_ne_zero_of_nonunit

@[simp]
theorem map_eq_zero [Semiring S] [Nontrivial S] (f : R →+* S) : p.map f = 0 ↔ p = 0 := by
  simp only [Polynomial.ext_iff]
  congr!
  simp [map_eq_zero, coeff_map, coeff_zero]

-- DISSOLVED: map_ne_zero

@[simp]
theorem degree_map [Semiring S] [Nontrivial S] (p : R[X]) (f : R →+* S) :
    degree (p.map f) = degree p :=
  p.degree_map_eq_of_injective f.injective

@[simp]
theorem natDegree_map [Semiring S] [Nontrivial S] (f : R →+* S) :
    natDegree (p.map f) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_map _ f)

@[simp]
theorem leadingCoeff_map [Semiring S] [Nontrivial S] (f : R →+* S) :
    leadingCoeff (p.map f) = f (leadingCoeff p) := by
  simp only [← coeff_natDegree, coeff_map f, natDegree_map]

theorem monic_map_iff [Semiring S] [Nontrivial S] {f : R →+* S} {p : R[X]} :
    (p.map f).Monic ↔ p.Monic := by
  rw [Monic, leadingCoeff_map, ← f.map_one, Function.Injective.eq_iff f.injective, Monic]

end DivisionRing

section Field

variable [Field R] {p q : R[X]}

-- DISSOLVED: isUnit_iff_degree_eq_zero

def div (p q : R[X]) :=
  C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹))

def mod (p q : R[X]) :=
  p %ₘ (q * C (leadingCoeff q)⁻¹)

private theorem quotient_mul_add_remainder_eq_aux (p q : R[X]) : q * div p q + mod p q = p := by
  by_cases h : q = 0
  · simp only [h, zero_mul, mod, modByMonic_zero, zero_add]
  · conv =>
      rhs
      rw [← modByMonic_add_div p (monic_mul_leadingCoeff_inv h)]
    rw [div, mod, add_comm, mul_assoc]

-- DISSOLVED: remainder_lt_aux

instance : Div R[X] :=
  ⟨div⟩

instance : Mod R[X] :=
  ⟨mod⟩

theorem div_def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) :=
  rfl

theorem mod_def : p % q = p %ₘ (q * C (leadingCoeff q)⁻¹) := rfl

theorem modByMonic_eq_mod (p : R[X]) (hq : Monic q) : p %ₘ q = p % q :=
  show p %ₘ q = p %ₘ (q * C (leadingCoeff q)⁻¹) by
    simp only [Monic.def.1 hq, inv_one, mul_one, C_1]

theorem divByMonic_eq_div (p : R[X]) (hq : Monic q) : p /ₘ q = p / q :=
  show p /ₘ q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) by
    simp only [Monic.def.1 hq, inv_one, C_1, one_mul, mul_one]

theorem mod_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p % (X - C a) = C (p.eval a) :=
  modByMonic_eq_mod p (monic_X_sub_C a) ▸ modByMonic_X_sub_C_eq_C_eval _ _

theorem mul_div_eq_iff_isRoot : (X - C a) * (p / (X - C a)) = p ↔ IsRoot p a :=
  divByMonic_eq_div p (monic_X_sub_C a) ▸ mul_divByMonic_eq_iff_isRoot

instance instEuclideanDomain : EuclideanDomain R[X] :=
  { Polynomial.commRing,
    Polynomial.nontrivial with
    quotient := (· / ·)
    quotient_zero := by simp [div_def]
    remainder := (· % ·)
    r := _
    r_wellFounded := degree_lt_wf
    quotient_mul_add_remainder_eq := quotient_mul_add_remainder_eq_aux
    remainder_lt := fun _ _ hq => remainder_lt_aux _ hq
    mul_left_not_lt := fun _ _ hq => not_lt_of_ge (degree_le_mul_left _ hq) }

-- DISSOLVED: mod_eq_self_iff

-- DISSOLVED: div_eq_zero_iff

-- DISSOLVED: degree_add_div

theorem degree_div_le (p q : R[X]) : degree (p / q) ≤ degree p := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [div_def, mul_comm, degree_mul_leadingCoeff_inv _ hq]; exact degree_divByMonic_le _ _

-- DISSOLVED: degree_div_lt

theorem isUnit_map [Field k] (f : R →+* k) : IsUnit (p.map f) ↔ IsUnit p := by
  simp_rw [isUnit_iff_degree_eq_zero, degree_map]

theorem map_div [Field k] (f : R →+* k) : (p / q).map f = p.map f / q.map f := by
  if hq0 : q = 0 then simp [hq0]
  else
    rw [div_def, div_def, Polynomial.map_mul, map_divByMonic f (monic_mul_leadingCoeff_inv hq0),
      Polynomial.map_mul, map_C, leadingCoeff_map, map_inv₀]

theorem map_mod [Field k] (f : R →+* k) : (p % q).map f = p.map f % q.map f := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [mod_def, mod_def, leadingCoeff_map f, ← map_inv₀ f, ← map_C f, ← Polynomial.map_mul f,
      map_modByMonic f (monic_mul_leadingCoeff_inv hq0)]

-- DISSOLVED: natDegree_mod_lt

section

open EuclideanDomain

theorem gcd_map [Field k] [DecidableEq R] [DecidableEq k] (f : R →+* k) :
    gcd (p.map f) (q.map f) = (gcd p q).map f :=
  GCD.induction p q (fun x => by simp_rw [Polynomial.map_zero, EuclideanDomain.gcd_zero_left])
    fun x y _ ih => by rw [gcd_val, ← map_mod, ih, ← gcd_val]

end

theorem eval₂_gcd_eq_zero [CommSemiring k] [DecidableEq R]
    {ϕ : R →+* k} {f g : R[X]} {α : k} (hf : f.eval₂ ϕ α = 0)
    (hg : g.eval₂ ϕ α = 0) : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 := by
  rw [EuclideanDomain.gcd_eq_gcd_ab f g, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_mul, hf, hg, zero_mul, zero_mul, zero_add]

theorem eval_gcd_eq_zero [DecidableEq R] {f g : R[X]} {α : R}
    (hf : f.eval α = 0) (hg : g.eval α = 0) : (EuclideanDomain.gcd f g).eval α = 0 :=
  eval₂_gcd_eq_zero hf hg

theorem root_left_of_root_gcd [CommSemiring k] [DecidableEq R] {ϕ : R →+* k} {f g : R[X]} {α : k}
    (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : f.eval₂ ϕ α = 0 := by
  cases' EuclideanDomain.gcd_dvd_left f g with p hp
  rw [hp, Polynomial.eval₂_mul, hα, zero_mul]

theorem root_right_of_root_gcd [CommSemiring k] [DecidableEq R] {ϕ : R →+* k} {f g : R[X]} {α : k}
    (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : g.eval₂ ϕ α = 0 := by
  cases' EuclideanDomain.gcd_dvd_right f g with p hp
  rw [hp, Polynomial.eval₂_mul, hα, zero_mul]

theorem root_gcd_iff_root_left_right [CommSemiring k] [DecidableEq R]
    {ϕ : R →+* k} {f g : R[X]} {α : k} :
    (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 ↔ f.eval₂ ϕ α = 0 ∧ g.eval₂ ϕ α = 0 :=
  ⟨fun h => ⟨root_left_of_root_gcd h, root_right_of_root_gcd h⟩, fun h => eval₂_gcd_eq_zero h.1 h.2⟩

theorem isRoot_gcd_iff_isRoot_left_right [DecidableEq R] {f g : R[X]} {α : R} :
    (EuclideanDomain.gcd f g).IsRoot α ↔ f.IsRoot α ∧ g.IsRoot α :=
  root_gcd_iff_root_left_right

theorem isCoprime_map [Field k] (f : R →+* k) : IsCoprime (p.map f) (q.map f) ↔ IsCoprime p q := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff, ← EuclideanDomain.gcd_isUnit_iff, gcd_map, isUnit_map]

-- DISSOLVED: mem_roots_map

-- DISSOLVED: rootSet_monomial

-- DISSOLVED: rootSet_C_mul_X_pow

-- DISSOLVED: rootSet_X_pow

-- DISSOLVED: rootSet_prod

theorem exists_root_of_degree_eq_one (h : degree p = 1) : ∃ x, IsRoot p x :=
  ⟨-(p.coeff 0 / p.coeff 1), by
    have : p.coeff 1 ≠ 0 := by
      have h' := natDegree_eq_of_degree_eq_some h
      change natDegree p = 1 at h'; rw [← h']
      exact mt leadingCoeff_eq_zero.1 fun h0 => by simp [h0] at h
    conv in p => rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1 by rw [h])]
    simp [IsRoot, mul_div_cancel₀ _ this]⟩

theorem coeff_inv_units (u : R[X]ˣ) (n : ℕ) : ((↑u : R[X]).coeff n)⁻¹ = (↑u⁻¹ : R[X]).coeff n := by
  rw [eq_C_of_degree_eq_zero (degree_coe_units u), eq_C_of_degree_eq_zero (degree_coe_units u⁻¹),
    coeff_C, coeff_C, inv_eq_one_div]
  split_ifs
  · rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero,
        coeff_zero_eq_eval_zero, ← eval_mul, ← Units.val_mul, inv_mul_cancel]
    simp
  · simp

-- DISSOLVED: monic_normalize

theorem leadingCoeff_div (hpq : q.degree ≤ p.degree) :
    (p / q).leadingCoeff = p.leadingCoeff / q.leadingCoeff := by
  by_cases hq : q = 0
  · simp [hq]
  rw [div_def, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_divByMonic_of_monic (monic_mul_leadingCoeff_inv hq) _, mul_comm,
    div_eq_mul_inv]
  rwa [degree_mul_leadingCoeff_inv q hq]

theorem div_C_mul : p / (C a * q) = C a⁻¹ * (p / q) := by
  by_cases ha : a = 0
  · simp [ha]
  simp only [div_def, leadingCoeff_mul, mul_inv, leadingCoeff_C, C.map_mul, mul_assoc]
  congr 3
  rw [mul_left_comm q, ← mul_assoc, ← C.map_mul, mul_inv_cancel₀ ha, C.map_one, one_mul]

-- DISSOLVED: C_mul_dvd

-- DISSOLVED: dvd_C_mul

-- DISSOLVED: coe_normUnit_of_ne_zero

theorem map_dvd_map' [Field k] (f : R →+* k) {x y : R[X]} : x.map f ∣ y.map f ↔ x ∣ y := by
  by_cases H : x = 0
  · rw [H, Polynomial.map_zero, zero_dvd_iff, zero_dvd_iff, map_eq_zero]
  · classical
    rw [← normalize_dvd_iff, ← @normalize_dvd_iff R[X], normalize_apply, normalize_apply,
      coe_normUnit_of_ne_zero H, coe_normUnit_of_ne_zero (mt (map_eq_zero f).1 H),
      leadingCoeff_map, ← map_inv₀ f, ← map_C, ← Polynomial.map_mul,
      map_dvd_map _ f.injective (monic_mul_leadingCoeff_inv H)]

@[simp]
theorem degree_normalize [DecidableEq R] : degree (normalize p) = degree p := by
  simp [normalize_apply]

theorem prime_of_degree_eq_one (hp1 : degree p = 1) : Prime p := by
  classical
  have : Prime (normalize p) :=
    Monic.prime_of_degree_eq_one (hp1 ▸ degree_normalize)
      (monic_normalize fun hp0 => absurd hp1 (hp0.symm ▸ by simp [degree_zero]))
  exact (normalize_associated _).prime this

theorem irreducible_of_degree_eq_one (hp1 : degree p = 1) : Irreducible p :=
  (prime_of_degree_eq_one hp1).irreducible

theorem not_irreducible_C (x : R) : ¬Irreducible (C x) := by
  by_cases H : x = 0
  · rw [H, C_0]
    exact not_irreducible_zero
  · exact fun hx => Irreducible.not_unit hx <| isUnit_C.2 <| isUnit_iff_ne_zero.2 H

theorem degree_pos_of_irreducible (hp : Irreducible p) : 0 < p.degree :=
  lt_of_not_ge fun hp0 =>
    have := eq_C_of_degree_le_zero hp0
    not_irreducible_C (p.coeff 0) <| this ▸ hp

theorem X_sub_C_mul_divByMonic_eq_sub_modByMonic {K : Type*} [Field K] (f : K[X]) (a : K) :
    (X - C a) * (f /ₘ (X - C a)) = f - f %ₘ (X - C a) := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', modByMonic_eq_sub_mul_div]
  exact monic_X_sub_C a

theorem divByMonic_add_X_sub_C_mul_derivate_divByMonic_eq_derivative
    {K : Type*} [Field K] (f : K[X]) (a : K) :
    f /ₘ (X - C a) + (X - C a) * derivative (f /ₘ (X - C a)) = derivative f := by
  have key := by apply congrArg derivative <| X_sub_C_mul_divByMonic_eq_sub_modByMonic f a
  rw [modByMonic_X_sub_C_eq_C_eval] at key
  rw [derivative_mul,derivative_sub,derivative_X,derivative_sub] at key
  rw [derivative_C,sub_zero,one_mul] at key
  rw [derivative_C,sub_zero] at key
  assumption

theorem X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic {K : Type*} [Field K] (f : K[X]) {a : K}
    (hf : (X - C a) ∣ f /ₘ (X - C a)) : X - C a ∣ derivative f := by
  have key := divByMonic_add_X_sub_C_mul_derivate_divByMonic_eq_derivative f a
  have ⟨u,hu⟩ := hf
  rw [← key, hu, ← mul_add (X - C a) u _]
  use (u + derivative ((X - C a) * u))

-- DISSOLVED: isCoprime_of_is_root_of_eval_derivative_ne_zero

-- DISSOLVED: irreducible_iff_degree_lt

-- DISSOLVED: irreducible_iff_lt_natDegree_lt

end Field

end Polynomial

theorem Irreducible.natDegree_pos {F : Type*} [Field F] {f : F[X]} (h : Irreducible f) :
    0 < f.natDegree := Nat.pos_of_ne_zero fun H ↦ by
  obtain ⟨x, hf⟩ := natDegree_eq_zero.1 H
  by_cases hx : x = 0
  · rw [← hf, hx, map_zero] at h; exact not_irreducible_zero h
  exact h.1 (hf ▸ isUnit_C.2 (Ne.isUnit hx))
