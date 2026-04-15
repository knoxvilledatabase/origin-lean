/-
Extracted from Algebra/Polynomial/Monic.lean
Genuine: 16 of 18 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Theory of monic polynomials

We give several tools for proving that polynomials are monic, e.g.
`Monic.mul`, `Monic.map`, `Monic.pow`.
-/

noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section Semiring

variable [Semiring R] {p q r : R[X]}

theorem monic_zero_iff_subsingleton : Monic (0 : R[X]) ↔ Subsingleton R :=
  subsingleton_iff_zero_eq_one

theorem not_monic_zero_iff : ¬Monic (0 : R[X]) ↔ (0 : R) ≠ 1 :=
  (monic_zero_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm).not

theorem monic_zero_iff_subsingleton' :
    Monic (0 : R[X]) ↔ (∀ f g : R[X], f = g) ∧ ∀ a b : R, a = b :=
  Polynomial.monic_zero_iff_subsingleton.trans
    ⟨by
      intro
      simp [eq_iff_true_of_subsingleton], fun h => subsingleton_iff.mpr h.2⟩

theorem Monic.as_sum (hp : p.Monic) :
    p = X ^ p.natDegree + ∑ i ∈ range p.natDegree, C (p.coeff i) * X ^ i := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, sum_range_succ_comm]
  suffices C (p.coeff p.natDegree) = 1 by rw [this, one_mul]
  exact congr_arg C hp

theorem Monic.map [Semiring S] (f : R →+* S) (hp : Monic p) : Monic (p.map f) :=
  subsingleton_or_nontrivial S |>.elim (·.elim ..) fun _ ↦
    f.map_one ▸ hp ▸ leadingCoeff_map_eq_of_isUnit_leadingCoeff _ <| isUnit_one

theorem monic_C_mul_of_mul_leadingCoeff_eq_one {b : R} (hp : b * p.leadingCoeff = 1) :
    Monic (C b * p) := by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

theorem monic_mul_C_of_leadingCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) :
    Monic (p * C b) := by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

theorem monic_X_pow_add {n : ℕ} (H : degree p < n) : Monic (X ^ n + p) :=
  monic_of_degree_le n
    (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H)))
    (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H, add_zero])

variable (a) in

-- DISSOLVED: monic_X_pow_add_C

theorem monic_X_add_C (x : R) : Monic (X + C x) :=
  pow_one (X : R[X]) ▸ monic_X_pow_add_C x one_ne_zero

theorem Monic.mul (hp : Monic p) (hq : Monic q) : Monic (p * q) :=
  letI := Classical.decEq R
  if h0 : (0 : R) = 1 then
    haveI := subsingleton_of_zero_eq_one h0
    Subsingleton.elim _ _
  else by
    have : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
      simp [Monic.def.1 hp, Monic.def.1 hq, Ne.symm h0]
    rw [Monic.def, leadingCoeff_mul' this, Monic.def.1 hp, Monic.def.1 hq, one_mul]

theorem Monic.pow (hp : Monic p) : ∀ n : ℕ, Monic (p ^ n)
  | 0 => monic_one
  | n + 1 => by
    rw [pow_succ]
    exact (Monic.pow hp n).mul hp

theorem Monic.add_of_left (hp : Monic p) (hpq : degree q < degree p) : Monic (p + q) := by
  rwa [Monic, add_comm, leadingCoeff_add_of_degree_lt hpq]

theorem Monic.add_of_right (hq : Monic q) (hpq : degree p < degree q) : Monic (p + q) := by
  rwa [Monic, leadingCoeff_add_of_degree_lt hpq]

theorem Monic.of_mul_monic_left (hp : p.Monic) (hpq : (p * q).Monic) : q.Monic := by
  contrapose hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_monic_mul hp]

theorem Monic.of_mul_monic_right (hq : q.Monic) (hpq : (p * q).Monic) : p.Monic := by
  contrapose hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_mul_monic hq]

namespace Monic

-- DISSOLVED: comp

lemma comp_X_add_C (hp : p.Monic) (r : R) : (p.comp (X + C r)).Monic := by
  nontriviality R
  refine hp.comp (monic_X_add_C _) fun ha ↦ ?_
  rw [natDegree_X_add_C] at ha
  exact one_ne_zero ha
