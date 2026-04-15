/-
Extracted from Algebra/Field/IsField.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

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
