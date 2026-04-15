/-
Extracted from Algebra/Polynomial/Degree/Lemmas.lean
Genuine: 15 of 24 | Dissolved: 9 | Infrastructure: 0
-/
import Origin.Core

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
              _ ≤ natDegree (C (coeff p n)) + n • ↑(natDegree q) := by grw [degree_le_natDegree]
              _ = (n * natDegree q : ℕ) := by
                rw [natDegree_C, Nat.cast_zero, zero_add, nsmul_eq_mul]
                simp
              _ ≤ (natDegree p * natDegree q : ℕ) :=
                WithBot.coe_le_coe.2 <|
                  by gcongr; exact le_natDegree_of_ne_zero (mem_support_iff.1 hn)

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

theorem natDegree_C_mul_le (a : R) (f : R[X]) : (C a * f).natDegree ≤ f.natDegree := by
  simpa using natDegree_mul_le (p := C a)

theorem natDegree_mul_C_le (f : R[X]) (a : R) : (f * C a).natDegree ≤ f.natDegree := by
  simpa using natDegree_mul_le (q := C a)

theorem eq_natDegree_of_le_mem_support (pn : p.natDegree ≤ n) (ns : n ∈ p.support) :
    p.natDegree = n :=
  le_antisymm pn (le_natDegree_of_mem_supp _ ns)

theorem natDegree_C_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) :
    (C a * p).natDegree = p.natDegree :=
  le_antisymm (natDegree_C_mul_le a p)
    (calc
      p.natDegree = (1 * p).natDegree := by nth_rw 1 [← one_mul p]
      _ = (C ai * (C a * p)).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ ≤ (C a * p).natDegree := natDegree_C_mul_le ai (C a * p))

theorem natDegree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) :
    (p * C a).natDegree = p.natDegree :=
  le_antisymm (natDegree_mul_C_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by nth_rw 1 [← mul_one p]
      _ = (p * C a * C ai).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ ≤ (p * C a).natDegree := natDegree_mul_C_le (p * C a) ai)

-- DISSOLVED: natDegree_mul_C_eq_of_mul_ne_zero

-- DISSOLVED: natDegree_C_mul_of_mul_ne_zero

-- DISSOLVED: degree_C_mul_of_mul_ne_zero

theorem natDegree_add_coeff_mul (f g : R[X]) :
    (f * g).coeff (f.natDegree + g.natDegree) = f.coeff f.natDegree * g.coeff g.natDegree := by
  simp only [coeff_natDegree, coeff_mul_degree_add_degree]

theorem natDegree_lt_coeff_mul (h : p.natDegree + q.natDegree < m + n) :
    (p * q).coeff (m + n) = 0 :=
  coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt h)

theorem coeff_pow_of_natDegree_le (pn : p.natDegree ≤ n) :
    (p ^ m).coeff (m * n) = p.coeff n ^ m := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ, pow_succ, ← hm, Nat.succ_mul, coeff_mul_add_eq_of_natDegree_le _ pn]
    refine natDegree_pow_le.trans (le_trans ?_ (le_refl _))
    gcongr

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

open scoped Function -- required for scoped `on` notation

-- DISSOLVED: degree_sum_eq_of_disjoint

-- DISSOLVED: natDegree_sum_eq_of_disjoint

variable [Semiring S]

-- DISSOLVED: natDegree_pos_of_eval₂_root

-- DISSOLVED: degree_pos_of_eval₂_root
