/-
Extracted from FieldTheory/Relrank.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Relative rank of subfields and intermediate fields

This file contains basics about the relative rank of subfields and intermediate fields.

## Main definitions

- `Subfield.relrank A B`, `IntermediateField.relrank A B`:
  defined to be `[B : A ⊓ B]` as a `Cardinal`.
  In particular, when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
  This is similar to `Subgroup.relIndex` but it is `Cardinal` valued.

- `Subfield.relfinrank A B`, `IntermediateField.relfinrank A B`:
  the `Nat` version of `Subfield.relrank A B` and `IntermediateField.relrank A B`, respectively.
  If `B / A ⊓ B` is an infinite extension, then it is zero.
  This is similar to `Subgroup.relIndex`.

-/

open Module Cardinal

universe u v w

namespace Subfield

variable {E : Type v} [Field E] {L : Type w} [Field L]

variable (A B C : Subfield E)

set_option backward.isDefEq.respectTransparency false in

noncomputable def relrank := Module.rank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))

noncomputable def relfinrank := finrank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))

variable {A B C}

theorem relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relrank A C = relrank B C := by
  simp_rw [relrank]
  congr!

theorem relfinrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relfinrank A C = relfinrank B C :=
  congr(toNat $(relrank_eq_of_inf_eq h))

set_option backward.isDefEq.respectTransparency false in

theorem relrank_eq_rank_of_le (h : A ≤ B) : relrank A B = Module.rank A (extendScalars h) := by
  rw [relrank]
  have := inf_of_le_left h
  congr!

theorem relfinrank_eq_finrank_of_le (h : A ≤ B) : relfinrank A B = finrank A (extendScalars h) :=
  congr(toNat $(relrank_eq_rank_of_le h))

variable (A B C)

theorem inf_relrank_right : relrank (A ⊓ B) B = relrank A B :=
  relrank_eq_rank_of_le (inf_le_right : A ⊓ B ≤ B)

theorem inf_relfinrank_right : relfinrank (A ⊓ B) B = relfinrank A B :=
  congr(toNat $(inf_relrank_right A B))

theorem inf_relrank_left : relrank (A ⊓ B) A = relrank B A := by
  rw [inf_comm, inf_relrank_right]

theorem inf_relfinrank_left : relfinrank (A ⊓ B) A = relfinrank B A :=
  congr(toNat $(inf_relrank_left A B))

set_option backward.isDefEq.respectTransparency false in
