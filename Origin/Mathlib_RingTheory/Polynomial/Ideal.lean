/-
Extracted from RingTheory/Polynomial/Ideal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ideals in polynomial rings
-/

noncomputable section

open Polynomial

open Finset

universe u v w

namespace Polynomial

variable {R : Type*} [CommRing R] {a : R}

theorem mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero {b : R[X]} {P : R[X][X]} :
    P ∈ Ideal.span {C (X - C a), X - C b} ↔ (P.eval b).eval a = 0 := by
  rw [Ideal.mem_span_pair]
  constructor <;> intro h
  · rcases h with ⟨_, _, rfl⟩
    simp
  · rcases dvd_iff_isRoot.mpr h with ⟨p, hp⟩
    rcases @X_sub_C_dvd_sub_C_eval _ b _ P with ⟨q, hq⟩
    exact ⟨C p, q, by rw [mul_comm, mul_comm q, eq_add_of_sub_eq' hq, hp, C_mul]⟩

theorem ker_evalRingHom (x : R) : RingHom.ker (evalRingHom x) = Ideal.span {X - C x} := by
  ext y
  simp [Ideal.mem_span_singleton, dvd_iff_isRoot, RingHom.mem_ker]
