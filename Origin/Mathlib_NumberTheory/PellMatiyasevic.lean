/-
Extracted from NumberTheory/PellMatiyasevic.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pell's equation and Matiyasevic's theorem

This file solves Pell's equation, i.e. integer solutions to `x ^ 2 - d * y ^ 2 = 1`
*in the special case that `d = a ^ 2 - 1`*.
This is then applied to prove Matiyasevic's theorem that the power
function is Diophantine, which is the last key ingredient in the solution to Hilbert's tenth
problem. For the definition of Diophantine function, see `NumberTheory.Dioph`.

For results on Pell's equation for arbitrary (positive, non-square) `d`, see
`NumberTheory.Pell`.

## Main definition

* `pell` is a function assigning to a natural number `n` the `n`-th solution to Pell's equation
  constructed recursively from the initial solution `(0, 1)`.

## Main statements

* `eq_pell` shows that every solution to Pell's equation is recursively obtained using `pell`
* `matiyasevic` shows that a certain system of Diophantine equations has a solution if and only if
  the first variable is the `x`-component in a solution to Pell's equation - the key step towards
  Hilbert's tenth problem in Davis' version of Matiyasevic's theorem.
* `eq_pow_of_pell` shows that the power function is Diophantine.

## Implementation notes

The proof of Matiyasevic's theorem doesn't follow Matiyasevic's original account of using Fibonacci
numbers but instead Davis' variant of using solutions to Pell's equation.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevič's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Pell's equation, Matiyasevic's theorem, Hilbert's tenth problem

-/

namespace Pell

open Nat

variable {d : ℤ}

def IsPell : ℤ√d → Prop
  | ⟨x, y⟩ => x * x - d * y * y = 1

theorem isPell_norm : ∀ {b : ℤ√d}, IsPell b ↔ b * star b = 1
  | ⟨x, y⟩ => by simp [Zsqrtd.ext_iff, IsPell, mul_comm]; ring_nf

theorem isPell_iff_mem_unitary : ∀ {b : ℤ√d}, IsPell b ↔ b ∈ unitary (ℤ√d)
  | ⟨x, y⟩ => by rw [Unitary.mem_iff, isPell_norm, mul_comm (star _), and_self_iff]

theorem isPell_mul {b c : ℤ√d} (hb : IsPell b) (hc : IsPell c) : IsPell (b * c) :=
  isPell_norm.2 (by simp [mul_comm, mul_left_comm c, mul_assoc,
    star_mul, isPell_norm.1 hb, isPell_norm.1 hc])

theorem isPell_star : ∀ {b : ℤ√d}, IsPell b ↔ IsPell (star b)
  | ⟨x, y⟩ => by simp [IsPell]

end

variable {a : ℕ} (a1 : 1 < a)

set_option backward.privateInPublic true in

private def d (_a1 : 1 < a) :=
  a * a - 1

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in
