/-
Extracted from Algebra/Polynomial/Div.lean
Genuine: 7 of 9 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Division of univariate polynomials

The main defs are `divByMonic` and `modByMonic`.
The compatibility between these is given by `modByMonic_add_div`.
We also define `rootMultiplicity`.
-/

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section Semiring

variable [Semiring R]

theorem X_dvd_iff {f : R[X]} : X ∣ f ↔ f.coeff 0 = 0 :=
  ⟨fun ⟨g, hfg⟩ => by rw [hfg, coeff_X_mul_zero], fun hf =>
    ⟨f.divX, by rw [← add_zero (X * f.divX), ← C_0, ← hf, X_mul_divX_add]⟩⟩

theorem X_pow_dvd_iff {f : R[X]} {n : ℕ} : X ^ n ∣ f ↔ ∀ d < n, f.coeff d = 0 :=
  ⟨fun ⟨g, hgf⟩ d hd => by
    simp only [hgf, coeff_X_pow_mul', ite_eq_right_iff, not_le_of_gt hd, IsEmpty.forall_iff],
    fun hd => by
    induction n with
    | zero => simp [pow_zero]
    | succ n hn =>
      obtain ⟨g, hgf⟩ := hn fun d : ℕ => fun H : d < n => hd _ (Nat.lt_succ_of_lt H)
      have := coeff_X_pow_mul g n 0
      rw [zero_add, ← hgf, hd n (Nat.lt_succ_self n)] at this
      obtain ⟨k, hgk⟩ := Polynomial.X_dvd_iff.mpr this.symm
      use k
      rwa [pow_succ, mul_assoc, ← hgk]⟩

variable {p q : R[X]}

-- DISSOLVED: finiteMultiplicity_of_degree_pos_of_monic

lemma eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le {p q : R[X]}
    (hp : p.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) :
    q = p * C q.leadingCoeff := by
  obtain ⟨r, rfl⟩ := hdvd
  obtain rfl | hr := eq_or_ne r 0
  · simp
  have : r.natDegree = 0 := by simpa [hp.natDegree_mul' hr] using hdeg
  rw [eq_C_of_natDegree_eq_zero this]
  simp [leadingCoeff_monic_mul hp]

lemma eq_of_monic_of_dvd_of_natDegree_le {p q : R[X]} (hp : p.Monic)
    (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) : q = p := by
  rw [eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le hp hdvd hdeg]
  simp [hq]

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

-- DISSOLVED: div_wf_lemma

noncomputable def divModByMonicAux : ∀ (_p : R[X]) {q : R[X]}, Monic q → R[X] × R[X]
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q ≤ degree p ∧ p ≠ 0 then
      let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
      have _wf := div_wf_lemma h hq
      let dm := divModByMonicAux (p - q * z) hq
      ⟨z + dm.1, dm.2⟩
    else ⟨0, p⟩
  termination_by p => p

def divByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).1 else 0

def modByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).2 else p
