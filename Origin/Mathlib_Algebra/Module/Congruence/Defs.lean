/-
Extracted from Algebra/Module/Congruence/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Congruence relations respecting scalar multiplication
-/

variable (R S M N : Type*)

structure VAddCon [VAdd S M] extends Setoid M where
  /-- A `VAddCon` is closed under additive action. -/
  vadd (s : S) {x y} : r x y → r (s +ᵥ x) (s +ᵥ y)
