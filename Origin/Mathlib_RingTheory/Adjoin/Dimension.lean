/-
Extracted from RingTheory/Adjoin/Dimension.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Some results on dimensions of algebra adjoin

This file contains some results on dimensions of `Algebra.adjoin`.
-/

open Module

universe u v

namespace Subalgebra

variable {R : Type u} {S : Type v} [CommRing R] [StrongRankCondition R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S) [Free R A] [Free R B]

theorem rank_sup_le_of_free : Module.rank R ↥(A ⊔ B) ≤ Module.rank R A * Module.rank R B := by
  obtain ⟨ιA, bA⟩ := Free.exists_basis (R := R) (M := A)
  obtain ⟨ιB, bB⟩ := Free.exists_basis (R := R) (M := B)
  have h := Algebra.adjoin_union_coe_submodule R (A : Set S) (B : Set S)
  rw [A.adjoin_eq_span_basis R bA, B.adjoin_eq_span_basis R bB, ← Algebra.sup_def,
    Submodule.span_mul_span] at h
  change Module.rank R ↥(toSubmodule (A ⊔ B)) ≤ _
  rw [h, ← bA.mk_eq_rank'', ← bB.mk_eq_rank'']
  refine (rank_span_le _).trans Cardinal.mk_mul_le |>.trans ?_
  gcongr <;> exact Cardinal.mk_range_le

end Subalgebra
