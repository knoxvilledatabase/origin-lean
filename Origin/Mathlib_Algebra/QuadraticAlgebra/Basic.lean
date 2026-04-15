/-
Extracted from Algebra/QuadraticAlgebra/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Quadratic algebras : involution and norm.

Let `R` be a commutative ring. We define:

* `QuadraticAlgebra.star` : the quadratic involution

* `QuadraticAlgebra.norm` : the norm

We prove :

* `QuadraticAlgebra.isUnit_iff_norm_isUnit`:
  `w : QuadraticAlgebra R a b` is a unit iff `w.norm` is a unit in `R`.

* `QuadraticAlgebra.norm_mem_nonZero_divisors_iff`:
  `w : QuadraticAlgebra R a b` isn't a zero divisor iff
  `w.norm` isn't a zero divisor in `R`.

* If `R` is a field, and `∀ r, r ^ 2 ≠ a + b * r`, then `QuadraticAlgebra R a b` is a field.

## Warning
If you are working over `ℚ`, note the existence of the diamond explained in
`Mathlib.Algebra.QuadraticAlgebra.Defs`.

-/

namespace QuadraticAlgebra

variable {R : Type*} {a b : R}

section omega

variable [Zero R] [One R]

def omega : QuadraticAlgebra R a b :=
  ⟨0, 1⟩

scoped notation "ω" => omega
