/-
Extracted from Algebra/CubicDiscriminant.lean
Genuine: 58 of 97 | Dissolved: 37 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.Splits

/-!
# Cubics and discriminants

This file defines cubic polynomials over a semiring and their discriminants over a splitting field.

## Main definitions

 * `Cubic`: the structure representing a cubic polynomial.
 * `Cubic.disc`: the discriminant of a cubic polynomial.

## Main statements

 * `Cubic.disc_ne_zero_iff_roots_nodup`: the cubic discriminant is not equal to zero if and only if
    the cubic has no duplicate roots.

## References

 * https://en.wikipedia.org/wiki/Cubic_equation
 * https://en.wikipedia.org/wiki/Discriminant

## Tags

cubic, discriminant, polynomial, root
-/

noncomputable section

@[ext]
structure Cubic (R : Type*) where
  (a b c d : R)

namespace Cubic

open Polynomial

variable {R S F K : Type*}

instance [Inhabited R] : Inhabited (Cubic R) :=
  ⟨⟨default, default, default, default⟩⟩

instance [Zero R] : Zero (Cubic R) :=
  ⟨⟨0, 0, 0, 0⟩⟩

section Basic

variable {P Q : Cubic R} {a b c d a' b' c' d' : R} [Semiring R]

def toPoly (P : Cubic R) : R[X] :=
  C P.a * X ^ 3 + C P.b * X ^ 2 + C P.c * X + C P.d

theorem C_mul_prod_X_sub_C_eq [CommRing S] {w x y z : S} :
    C w * (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨w, w * -(x + y + z), w * (x * y + x * z + y * z), w * -(x * y * z)⟩ := by
  simp only [toPoly, C_neg, C_add, C_mul]
  ring1

theorem prod_X_sub_C_eq [CommRing S] {x y z : S} :
    (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨1, -(x + y + z), x * y + x * z + y * z, -(x * y * z)⟩ := by
  rw [← one_mul <| X - C x, ← C_1, C_mul_prod_X_sub_C_eq, one_mul, one_mul, one_mul]

/-! ### Coefficients -/

section Coeff

private theorem coeffs : (∀ n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
    P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d := by
  simp only [toPoly, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num
  intro n hn
  repeat' rw [if_neg]
  any_goals linarith only [hn]
  repeat' rw [zero_add]

@[simp]
theorem coeff_eq_zero {n : ℕ} (hn : 3 < n) : P.toPoly.coeff n = 0 :=
  coeffs.1 n hn

@[simp]
theorem coeff_eq_a : P.toPoly.coeff 3 = P.a :=
  coeffs.2.1

@[simp]
theorem coeff_eq_b : P.toPoly.coeff 2 = P.b :=
  coeffs.2.2.1

@[simp]
theorem coeff_eq_c : P.toPoly.coeff 1 = P.c :=
  coeffs.2.2.2.1

@[simp]
theorem coeff_eq_d : P.toPoly.coeff 0 = P.d :=
  coeffs.2.2.2.2

theorem a_of_eq (h : P.toPoly = Q.toPoly) : P.a = Q.a := by rw [← coeff_eq_a, h, coeff_eq_a]

theorem b_of_eq (h : P.toPoly = Q.toPoly) : P.b = Q.b := by rw [← coeff_eq_b, h, coeff_eq_b]

theorem c_of_eq (h : P.toPoly = Q.toPoly) : P.c = Q.c := by rw [← coeff_eq_c, h, coeff_eq_c]

theorem d_of_eq (h : P.toPoly = Q.toPoly) : P.d = Q.d := by rw [← coeff_eq_d, h, coeff_eq_d]

theorem toPoly_injective (P Q : Cubic R) : P.toPoly = Q.toPoly ↔ P = Q :=
  ⟨fun h ↦ Cubic.ext (a_of_eq h) (b_of_eq h) (c_of_eq h) (d_of_eq h), congr_arg toPoly⟩

theorem of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^ 2 + C P.c * X + C P.d := by
  rw [toPoly, ha, C_0, zero_mul, zero_add]

theorem of_a_eq_zero' : toPoly ⟨0, b, c, d⟩ = C b * X ^ 2 + C c * X + C d :=
  of_a_eq_zero rfl

theorem of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly = C P.c * X + C P.d := by
  rw [of_a_eq_zero ha, hb, C_0, zero_mul, zero_add]

theorem of_b_eq_zero' : toPoly ⟨0, 0, c, d⟩ = C c * X + C d :=
  of_b_eq_zero rfl rfl

theorem of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly = C P.d := by
  rw [of_b_eq_zero ha hb, hc, C_0, zero_mul, zero_add]

theorem of_c_eq_zero' : toPoly ⟨0, 0, 0, d⟩ = C d :=
  of_c_eq_zero rfl rfl rfl

theorem of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly = 0 := by
  rw [of_c_eq_zero ha hb hc, hd, C_0]

theorem of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly = 0 :=
  of_d_eq_zero rfl rfl rfl rfl

theorem zero : (0 : Cubic R).toPoly = 0 :=
  of_d_eq_zero'

theorem toPoly_eq_zero_iff (P : Cubic R) : P.toPoly = 0 ↔ P = 0 := by
  rw [← zero, toPoly_injective]

-- DISSOLVED: ne_zero

-- DISSOLVED: ne_zero_of_a_ne_zero

-- DISSOLVED: ne_zero_of_b_ne_zero

-- DISSOLVED: ne_zero_of_c_ne_zero

-- DISSOLVED: ne_zero_of_d_ne_zero

-- DISSOLVED: leadingCoeff_of_a_ne_zero

-- DISSOLVED: leadingCoeff_of_a_ne_zero'

-- DISSOLVED: leadingCoeff_of_b_ne_zero

-- DISSOLVED: leadingCoeff_of_b_ne_zero'

-- DISSOLVED: leadingCoeff_of_c_ne_zero

-- DISSOLVED: leadingCoeff_of_c_ne_zero'

@[simp]
theorem leadingCoeff_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.leadingCoeff = P.d := by
  rw [of_c_eq_zero ha hb hc, leadingCoeff_C]

theorem leadingCoeff_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).leadingCoeff = d :=
  leadingCoeff_of_c_eq_zero rfl rfl rfl

theorem monic_of_a_eq_one (ha : P.a = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff_of_a_ne_zero (ha ▸ one_ne_zero), ha]

theorem monic_of_a_eq_one' : (toPoly ⟨1, b, c, d⟩).Monic :=
  monic_of_a_eq_one rfl

theorem monic_of_b_eq_one (ha : P.a = 0) (hb : P.b = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff_of_b_ne_zero ha (hb ▸ one_ne_zero), hb]

theorem monic_of_b_eq_one' : (toPoly ⟨0, 1, c, d⟩).Monic :=
  monic_of_b_eq_one rfl rfl

theorem monic_of_c_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff_of_c_ne_zero ha hb (hc ▸ one_ne_zero), hc]

theorem monic_of_c_eq_one' : (toPoly ⟨0, 0, 1, d⟩).Monic :=
  monic_of_c_eq_one rfl rfl rfl

theorem monic_of_d_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 1) :
    P.toPoly.Monic := by
  rw [Monic, leadingCoeff_of_c_eq_zero ha hb hc, hd]

theorem monic_of_d_eq_one' : (toPoly ⟨0, 0, 0, 1⟩).Monic :=
  monic_of_d_eq_one rfl rfl rfl rfl

end Coeff

/-! ### Degrees -/

section Degree

@[simps]
def equiv : Cubic R ≃ { p : R[X] // p.degree ≤ 3 } where
  toFun P := ⟨P.toPoly, degree_cubic_le⟩
  invFun f := ⟨coeff f 3, coeff f 2, coeff f 1, coeff f 0⟩
  left_inv P := by ext <;> simp only [Subtype.coe_mk, coeffs]
  right_inv f := by
    -- Porting note: Added `simp only [Nat.succ_eq_add_one] <;> ring_nf`
    -- There's probably a better way to do this.
    ext (_ | _ | _ | _ | n) <;> simp only [Nat.succ_eq_add_one] <;> ring_nf
      <;> try simp only [coeffs]
    have h3 : 3 < 4 + n := by linarith only
    rw [coeff_eq_zero h3,
      (degree_le_iff_coeff_zero (f : R[X]) 3).mp f.2 _ <| WithBot.coe_lt_coe.mpr (by exact h3)]

-- DISSOLVED: degree_of_a_ne_zero

-- DISSOLVED: degree_of_a_ne_zero'

theorem degree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.degree ≤ 2 := by
  simpa only [of_a_eq_zero ha] using degree_quadratic_le

theorem degree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).degree ≤ 2 :=
  degree_of_a_eq_zero rfl

-- DISSOLVED: degree_of_b_ne_zero

-- DISSOLVED: degree_of_b_ne_zero'

theorem degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.degree ≤ 1 := by
  simpa only [of_b_eq_zero ha hb] using degree_linear_le

theorem degree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).degree ≤ 1 :=
  degree_of_b_eq_zero rfl rfl

-- DISSOLVED: degree_of_c_ne_zero

-- DISSOLVED: degree_of_c_ne_zero'

theorem degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly.degree ≤ 0 := by
  simpa only [of_c_eq_zero ha hb hc] using degree_C_le

theorem degree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).degree ≤ 0 :=
  degree_of_c_eq_zero rfl rfl rfl

-- DISSOLVED: degree_of_d_ne_zero

-- DISSOLVED: degree_of_d_ne_zero'

@[simp]
theorem degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly.degree = ⊥ := by
  rw [of_d_eq_zero ha hb hc hd, degree_zero]

theorem degree_of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero rfl rfl rfl rfl

@[simp]
theorem degree_of_zero : (0 : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero'

-- DISSOLVED: natDegree_of_a_ne_zero

-- DISSOLVED: natDegree_of_a_ne_zero'

theorem natDegree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.natDegree ≤ 2 := by
  simpa only [of_a_eq_zero ha] using natDegree_quadratic_le

theorem natDegree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).natDegree ≤ 2 :=
  natDegree_of_a_eq_zero rfl

-- DISSOLVED: natDegree_of_b_ne_zero

-- DISSOLVED: natDegree_of_b_ne_zero'

theorem natDegree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.natDegree ≤ 1 := by
  simpa only [of_b_eq_zero ha hb] using natDegree_linear_le

theorem natDegree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).natDegree ≤ 1 :=
  natDegree_of_b_eq_zero rfl rfl

-- DISSOLVED: natDegree_of_c_ne_zero

-- DISSOLVED: natDegree_of_c_ne_zero'

@[simp]
theorem natDegree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.natDegree = 0 := by
  rw [of_c_eq_zero ha hb hc, natDegree_C]

theorem natDegree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).natDegree = 0 :=
  natDegree_of_c_eq_zero rfl rfl rfl

@[simp]
theorem natDegree_of_zero : (0 : Cubic R).toPoly.natDegree = 0 :=
  natDegree_of_c_eq_zero'

end Degree

/-! ### Map across a homomorphism -/

section Map

variable [Semiring S] {φ : R →+* S}

def map (φ : R →+* S) (P : Cubic R) : Cubic S :=
  ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩

theorem map_toPoly : (map φ P).toPoly = Polynomial.map φ P.toPoly := by
  simp only [map, toPoly, map_C, map_X, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

end Map

end Basic

section Roots

open Multiset

/-! ### Roots over an extension -/

section Extension

variable {P : Cubic R} [CommRing R] [CommRing S] {φ : R →+* S}

def roots [IsDomain R] (P : Cubic R) : Multiset R :=
  P.toPoly.roots

theorem map_roots [IsDomain S] : (map φ P).roots = (Polynomial.map φ P.toPoly).roots := by
  rw [roots, map_toPoly]

-- DISSOLVED: mem_roots_iff

theorem card_roots_le [IsDomain R] [DecidableEq R] : P.roots.toFinset.card ≤ 3 := by
  apply (toFinset_card_le P.toPoly.roots).trans
  by_cases hP : P.toPoly = 0
  · exact (card_roots' P.toPoly).trans (by rw [hP, natDegree_zero]; exact zero_le 3)
  · exact WithBot.coe_le_coe.1 ((card_roots hP).trans degree_cubic_le)

end Extension

variable {P : Cubic F} [Field F] [Field K] {φ : F →+* K} {x y z : K}

/-! ### Roots over a splitting field -/

section Split

-- DISSOLVED: splits_iff_card_roots

-- DISSOLVED: splits_iff_roots_eq_three

-- DISSOLVED: eq_prod_three_roots

-- DISSOLVED: eq_sum_three_roots

-- DISSOLVED: b_eq_three_roots

-- DISSOLVED: c_eq_three_roots

-- DISSOLVED: d_eq_three_roots

end Split

/-! ### Discriminant over a splitting field -/

section Discriminant

def disc {R : Type*} [Ring R] (P : Cubic R) : R :=
  P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2 +
    18 * P.a * P.b * P.c * P.d

-- DISSOLVED: disc_eq_prod_three_roots

-- DISSOLVED: disc_ne_zero_iff_roots_ne

-- DISSOLVED: disc_ne_zero_iff_roots_nodup

-- DISSOLVED: card_roots_of_disc_ne_zero

end Discriminant

end Roots

end Cubic
