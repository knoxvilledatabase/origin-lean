/-
Extracted from LinearAlgebra/AffineSpace/MidpointZero.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Midpoint of a segment for characteristic zero

We collect lemmas that require that the underlying ring has characteristic zero.

## Tags

midpoint
-/

open AffineMap AffineEquiv

theorem lineMap_one_half {R : Type*} {V P : Type*} [DivisionRing R] [CharZero R] [AddCommGroup V]
    [Module R V] [AddTorsor V P] (a b : P) : lineMap a b (1 / 2 : R) = midpoint R a b := by
  rw [one_div, lineMap_inv_two]

theorem homothety_one_half {k : Type*} {V P : Type*} [Field k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (a b : P) : homothety a (1 / 2 : k) b = midpoint k a b := by
  rw [one_div, homothety_inv_two]
