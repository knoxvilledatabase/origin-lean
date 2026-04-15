/-
Extracted from Algebra/Field/IsField.lean
Genuine: 5 of 8 | Dissolved: 2 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Common

/-!
# `IsField` predicate

Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
commutative, that it has more than one element and that all non-zero elements have a
multiplicative inverse. In contrast to `Field`, which contains the data of a function associating
to an element of the field its multiplicative inverse, this predicate only assumes the existence
and can therefore more easily be used to e.g. transfer along ring isomorphisms.
-/

universe u

section IsField

-- DISSOLVED: IsField

theorem Semifield.toIsField (R : Type u) [Semifield R] : IsField R where
  __ := ‹Semifield R›
  mul_inv_cancel {a} ha := ⟨a⁻¹, mul_inv_cancel₀ ha⟩

theorem Field.toIsField (R : Type u) [Field R] : IsField R :=
  Semifield.toIsField _

@[simp]
theorem IsField.nontrivial {R : Type u} [Semiring R] (h : IsField R) : Nontrivial R :=
  ⟨h.exists_pair_ne⟩

@[simp]
theorem not_isField_of_subsingleton (R : Type u) [Semiring R] [Subsingleton R] : ¬IsField R :=
  fun h =>
  let ⟨_, _, h⟩ := h.exists_pair_ne
  h (Subsingleton.elim _ _)

open Classical in

noncomputable def IsField.toSemifield {R : Type u} [Semiring R] (h : IsField R) : Semifield R where
  __ := ‹Semiring R›
  __ := h
  inv a := if ha : a = 0 then 0 else Classical.choose (h.mul_inv_cancel ha)
  inv_zero := dif_pos rfl
  mul_inv_cancel a ha := by convert Classical.choose_spec (h.mul_inv_cancel ha); exact dif_neg ha
  nnqsmul := _
  nnqsmul_def _ _ := rfl

noncomputable def IsField.toField {R : Type u} [Ring R] (h : IsField R) : Field R :=
  { ‹Ring R›, IsField.toSemifield h with
    qsmul := _
    qsmul_def := fun _ _ => rfl }

-- DISSOLVED: uniq_inv_of_isField

end IsField
