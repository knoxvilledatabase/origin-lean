/-
Extracted from FieldTheory/Perfect.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# Perfect fields and rings

In this file we define perfect fields, together with a generalisation to (commutative) rings in
prime characteristic.

## Main definitions / statements:
* `PerfectRing`: a ring of characteristic `p` (prime) is said to be perfect in the sense of Serre,
  if its absolute Frobenius map `x ↦ xᵖ` is bijective.
* `PerfectField`: a field `K` is said to be perfect if every irreducible polynomial over `K` is
  separable.
* `PerfectRing.toPerfectField`: a field that is perfect in the sense of Serre is a perfect field.
* `PerfectField.toPerfectRing`: a perfect field of characteristic `p` (prime) is perfect in the
  sense of Serre.
* `PerfectField.ofCharZero`: all fields of characteristic zero are perfect.
* `PerfectField.ofFinite`: all finite fields are perfect.
* `PerfectField.separable_iff_squarefree`: a polynomial over a perfect field is separable iff
  it is square-free.
* `Algebra.IsAlgebraic.isSeparable_of_perfectField`, `Algebra.IsAlgebraic.perfectField`:
  if `L / K` is an algebraic extension, `K` is a perfect field, then `L / K` is separable,
  and `L` is also a perfect field.

-/

open Function Polynomial

class PerfectRing (R : Type*) (p : ℕ) [Pow R ℕ] : Prop where
  /-- A ring is perfect if the Frobenius map is bijective. -/
  bijective_frobenius : Bijective fun x : R ↦ x ^ p

section PerfectRing

section Monoid

variable (M : Type*) (p q : ℕ) [CommMonoid M] [PerfectRing M p] [PerfectRing M q]

namespace PerfectRing

-- INSTANCE (free from Core): one

-- INSTANCE (free from Core): mul

-- INSTANCE (free from Core): pow

end PerfectRing
