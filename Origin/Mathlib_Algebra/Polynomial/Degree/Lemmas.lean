/-
Extracted from Algebra/Polynomial/Degree/Lemmas.lean
Genuine: 30 | Conflates: 0 | Dissolved: 23 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Prime.Lemmas

/-!
# Theory of degrees of polynomials

Some of the main results include
- `natDegree_comp_le` : The degree of the composition is at most the product of degrees

-/

noncomputable section

open Polynomial

open Finsupp Finset

namespace Polynomial

universe u v w

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section Degree

theorem natDegree_comp_le : natDegree (p.comp q) ≤ natDegree p * natDegree q :=
  letI := Classical.decEq R
  if h0 : p.comp q = 0 then by rw [h0, natDegree_zero]; exact Nat.zero_le _
  else
    WithBot.coe_le_coe.1 <|
      calc
        ↑(natDegree (p.comp q)) = degree (p.comp q) := (degree_eq_natDegree h0).symm
        _ = _ := congr_arg degree comp_eq_sum_left
        _ ≤ _ := degree_sum_le _ _
        _ ≤ _ :=
          Finset.sup_le fun n hn =>
            calc
              degree (C (coeff p n) * q ^ n) ≤ degree (C (coeff p n)) + degree (q ^ n) :=
                degree_mul_le _ _
              _ ≤ natDegree (C (coeff p n)) + n • degree q :=
                (add_le_add degree_le_natDegree (degree_pow_le _ _))
              _ ≤ natDegree (C (coeff p n)) + n • ↑(natDegree q) :=
                (add_le_add_left (nsmul_le_nsmul_right (@degree_le_natDegree _ _ q) n) _)
              _ = (n * natDegree q : ℕ) := by
                rw [natDegree_C, Nat.cast_zero, zero_add, nsmul_eq_mul]
                simp
              _ ≤ (natDegree p * natDegree q : ℕ) :=
                WithBot.coe_le_coe.2 <|
                  mul_le_mul_of_nonneg_right (le_natDegree_of_ne_zero (mem_support_iff.1 hn))
                    (Nat.zero_le _)

-- DISSOLVED: natDegree_comp_eq_of_mul_ne_zero

-- DISSOLVED: degree_pos_of_root

theorem natDegree_le_iff_coeff_eq_zero : p.natDegree ≤ n ↔ ∀ N : ℕ, n < N → p.coeff N = 0 := by
  simp_rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero, Nat.cast_lt]

theorem natDegree_add_le_iff_left {n : ℕ} (p q : R[X]) (qn : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  refine ⟨fun h => ?_, fun h => natDegree_add_le_of_degree_le h qn⟩
  refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  convert natDegree_le_iff_coeff_eq_zero.mp h m hm using 1
  rw [coeff_add, natDegree_le_iff_coeff_eq_zero.mp qn _ hm, add_zero]

theorem natDegree_add_le_iff_right {n : ℕ} (p q : R[X]) (pn : p.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ q.natDegree ≤ n := by
  rw [add_comm]
  exact natDegree_add_le_iff_left _ _ pn

theorem natDegree_C_mul_le (a : R) (f : R[X]) : (C a * f).natDegree ≤ f.natDegree :=
  calc
    (C a * f).natDegree ≤ (C a).natDegree + f.natDegree := natDegree_mul_le
    _ = 0 + f.natDegree := by rw [natDegree_C a]
    _ = f.natDegree := zero_add _

theorem natDegree_mul_C_le (f : R[X]) (a : R) : (f * C a).natDegree ≤ f.natDegree :=
  calc
    (f * C a).natDegree ≤ f.natDegree + (C a).natDegree := natDegree_mul_le
    _ = f.natDegree + 0 := by rw [natDegree_C a]
    _ = f.natDegree := add_zero _

theorem eq_natDegree_of_le_mem_support (pn : p.natDegree ≤ n) (ns : n ∈ p.support) :
    p.natDegree = n :=
  le_antisymm pn (le_natDegree_of_mem_supp _ ns)

theorem natDegree_C_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) :
    (C a * p).natDegree = p.natDegree :=
  le_antisymm (natDegree_C_mul_le a p)
    (calc
      p.natDegree = (1 * p).natDegree := by nth_rw 1 [← one_mul p]
      _ = (C ai * (C a * p)).natDegree := by rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
      _ ≤ (C a * p).natDegree := natDegree_C_mul_le ai (C a * p))

theorem natDegree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) :
    (p * C a).natDegree = p.natDegree :=
  le_antisymm (natDegree_mul_C_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by nth_rw 1 [← mul_one p]
      _ = (p * C a * C ai).natDegree := by rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
      _ ≤ (p * C a).natDegree := natDegree_mul_C_le (p * C a) ai)

-- DISSOLVED: natDegree_mul_C_eq_of_mul_ne_zero

-- DISSOLVED: natDegree_C_mul_eq_of_mul_ne_zero

theorem natDegree_add_coeff_mul (f g : R[X]) :
    (f * g).coeff (f.natDegree + g.natDegree) = f.coeff f.natDegree * g.coeff g.natDegree := by
  simp only [coeff_natDegree, coeff_mul_degree_add_degree]

theorem natDegree_lt_coeff_mul (h : p.natDegree + q.natDegree < m + n) :
    (p * q).coeff (m + n) = 0 :=
  coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt h)

theorem coeff_mul_of_natDegree_le (pm : p.natDegree ≤ m) (qn : q.natDegree ≤ n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  simp_rw [← Polynomial.toFinsupp_apply, toFinsupp_mul]
  refine AddMonoidAlgebra.apply_add_of_supDegree_le ?_ Function.injective_id ?_ ?_
  · simp
  · rwa [supDegree_eq_natDegree, id_eq]
  · rwa [supDegree_eq_natDegree, id_eq]

theorem coeff_pow_of_natDegree_le (pn : p.natDegree ≤ n) :
    (p ^ m).coeff (m * n) = p.coeff n ^ m := by
  induction' m with m hm
  · simp
  · rw [pow_succ, pow_succ, ← hm, Nat.succ_mul, coeff_mul_of_natDegree_le _ pn]
    refine natDegree_pow_le.trans (le_trans ?_ (le_refl _))
    exact mul_le_mul_of_nonneg_left pn m.zero_le

theorem coeff_pow_eq_ite_of_natDegree_le_of_le {o : ℕ}
    (pn : natDegree p ≤ n) (mno : m * n ≤ o) :
    coeff (p ^ m) o = if o = m * n then (coeff p n) ^ m else 0 := by
  rcases eq_or_ne o (m * n) with rfl | h
  · simpa only [ite_true] using coeff_pow_of_natDegree_le pn
  · simpa only [h, ite_false] using coeff_eq_zero_of_natDegree_lt <|
      lt_of_le_of_lt (natDegree_pow_le_of_le m pn) (lt_of_le_of_ne mno h.symm)

theorem coeff_add_eq_left_of_lt (qn : q.natDegree < n) : (p + q).coeff n = p.coeff n :=
  (coeff_add _ _ _).trans <|
    (congr_arg _ <| coeff_eq_zero_of_natDegree_lt <| qn).trans <| add_zero _

theorem coeff_add_eq_right_of_lt (pn : p.natDegree < n) : (p + q).coeff n = q.coeff n := by
  rw [add_comm]
  exact coeff_add_eq_left_of_lt pn

-- DISSOLVED: degree_sum_eq_of_disjoint

-- DISSOLVED: natDegree_sum_eq_of_disjoint

variable [Semiring S]

-- DISSOLVED: natDegree_pos_of_eval₂_root

-- DISSOLVED: degree_pos_of_eval₂_root

@[simp]
theorem coe_lt_degree {p : R[X]} {n : ℕ} : (n : WithBot ℕ) < degree p ↔ n < natDegree p := by
  by_cases h : p = 0
  · simp [h]
  simp [degree_eq_natDegree h, Nat.cast_lt]

-- DISSOLVED: degree_map_eq_iff

-- DISSOLVED: natDegree_map_eq_iff

-- DISSOLVED: natDegree_pos_of_nextCoeff_ne_zero

end Degree

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

theorem natDegree_sub : (p - q).natDegree = (q - p).natDegree := by rw [← natDegree_neg, neg_sub]

theorem natDegree_sub_le_iff_left (qn : q.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  rw [← natDegree_neg] at qn
  rw [sub_eq_add_neg, natDegree_add_le_iff_left _ _ qn]

theorem natDegree_sub_le_iff_right (pn : p.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ q.natDegree ≤ n := by rwa [natDegree_sub, natDegree_sub_le_iff_left]

theorem coeff_sub_eq_left_of_lt (dg : q.natDegree < n) : (p - q).coeff n = p.coeff n := by
  rw [← natDegree_neg] at dg
  rw [sub_eq_add_neg, coeff_add_eq_left_of_lt dg]

theorem coeff_sub_eq_neg_right_of_lt (df : p.natDegree < n) : (p - q).coeff n = -q.coeff n := by
  rwa [sub_eq_add_neg, coeff_add_eq_right_of_lt, coeff_neg]

end Ring

section NoZeroDivisors

variable [Semiring R] {p q : R[X]} {a : R}

-- DISSOLVED: nextCoeff_C_mul_X_add_C

-- DISSOLVED: natDegree_eq_one

variable [NoZeroDivisors R]

-- DISSOLVED: degree_mul_C

-- DISSOLVED: degree_C_mul

-- DISSOLVED: natDegree_mul_C

-- DISSOLVED: natDegree_C_mul

theorem natDegree_comp : natDegree (p.comp q) = natDegree p * natDegree q := by
  by_cases q0 : q.natDegree = 0
  · rw [degree_le_zero_iff.mp (natDegree_eq_zero_iff_degree_le_zero.mp q0), comp_C, natDegree_C,
      natDegree_C, mul_zero]
  · by_cases p0 : p = 0
    · simp only [p0, zero_comp, natDegree_zero, zero_mul]
    · simp only [Ne, mul_eq_zero, leadingCoeff_eq_zero, p0, natDegree_comp_eq_of_mul_ne_zero,
        ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero q0), not_false_eq_true, pow_ne_zero, or_self]

@[simp]
theorem natDegree_iterate_comp (k : ℕ) :
    (p.comp^[k] q).natDegree = p.natDegree ^ k * q.natDegree := by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', natDegree_comp, IH, pow_succ', mul_assoc]

-- DISSOLVED: leadingCoeff_comp

end NoZeroDivisors

section CommRing

variable [CommRing R] {p q : R[X]}

@[simp] lemma comp_neg_X_leadingCoeff_eq (p : R[X]) :
    (p.comp (-X)).leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff := by
  nontriviality R
  by_cases h : p = 0
  · simp [h]
  rw [Polynomial.leadingCoeff, natDegree_comp_eq_of_mul_ne_zero, coeff_comp_degree_mul_degree] <;>
  simp [mul_comm, h]

variable [IsDomain R]

lemma comp_eq_zero_iff : p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = C (q.coeff 0) := by
  refine ⟨fun h ↦ ?_, Or.rec (fun h ↦ by simp [h]) fun h ↦ by rw [h.2, comp_C, h.1, C_0]⟩
  have key : p.natDegree = 0 ∨ q.natDegree = 0 := by
    rw [← mul_eq_zero, ← natDegree_comp, h, natDegree_zero]
  obtain key | key := Or.imp eq_C_of_natDegree_eq_zero eq_C_of_natDegree_eq_zero key
  · rw [key, C_comp] at h
    exact Or.inl (key.trans h)
  · rw [key, comp_C, C_eq_zero] at h
    exact Or.inr ⟨h, key⟩

end CommRing

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-! Useful lemmas for the "monicization" of a nonzero polynomial `p`. -/

@[simp]
theorem irreducible_mul_leadingCoeff_inv {p : K[X]} :
    Irreducible (p * C (leadingCoeff p)⁻¹) ↔ Irreducible p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact irreducible_mul_isUnit
    (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))

-- DISSOLVED: dvd_mul_leadingCoeff_inv

-- DISSOLVED: monic_mul_leadingCoeff_inv

-- DISSOLVED: degree_leadingCoeff_inv

-- DISSOLVED: degree_mul_leadingCoeff_inv

-- DISSOLVED: natDegree_mul_leadingCoeff_inv

theorem degree_mul_leadingCoeff_self_inv (p : K[X]) :
    degree (p * C (leadingCoeff p)⁻¹) = degree p := by
  by_cases hp : p = 0
  · simp [hp]
  exact degree_mul_leadingCoeff_inv _ hp

theorem natDegree_mul_leadingCoeff_self_inv (p : K[X]) :
    natDegree (p * C (leadingCoeff p)⁻¹) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_self_inv _)

@[simp] lemma degree_add_degree_leadingCoeff_inv (p : K[X]) :
    degree p + degree (C (leadingCoeff p)⁻¹) = degree p := by
  rw [← degree_mul, degree_mul_leadingCoeff_self_inv]

end DivisionRing

end Polynomial
