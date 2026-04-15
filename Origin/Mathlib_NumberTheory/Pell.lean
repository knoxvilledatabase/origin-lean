/-
Extracted from NumberTheory/Pell.lean
Genuine: 7 of 11 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Pell's Equation

*Pell's Equation* is the equation $x^2 - d y^2 = 1$, where $d$ is a positive integer
that is not a square, and one is interested in solutions in integers $x$ and $y$.

In this file, we aim at providing all of the essential theory of Pell's Equation for general $d$
(as opposed to the contents of `NumberTheory.PellMatiyasevic`, which is specific to the case
$d = a^2 - 1$ for some $a > 1$).

We begin by defining a type `Pell.Solution₁ d` for solutions of the equation,
show that it has a natural structure as an abelian group, and prove some basic
properties.

We then prove the following

**Theorem.** Let $d$ be a positive integer that is not a square. Then the equation
$x^2 - d y^2 = 1$ has a nontrivial (i.e., with $y \ne 0$) solution in integers.

See `Pell.exists_of_not_isSquare` and `Pell.Solution₁.exists_nontrivial_of_not_isSquare`.

We then define the *fundamental solution* to be the solution
with smallest $x$ among all solutions satisfying $x > 1$ and $y > 0$.
We show that every solution is a power (in the sense of the group structure mentioned above)
of the fundamental solution up to a (common) sign,
see `Pell.IsFundamental.eq_zpow_or_neg_zpow`, and that a (positive) solution has this property
if and only if it is fundamental, see `Pell.pos_generator_iff_fundamental`.

## References

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory* (Section 17.5)]
  [IrelandRosen1990]

## Tags

Pell's equation

## TODO

* Extend to `x ^ 2 - d * y ^ 2 = -1` and further generalizations.
* Connect solutions to the continued fraction expansion of `√d`.
-/

namespace Pell

/-!
### Group structure of the solution set

We define a structure of a commutative multiplicative group with distributive negation
on the set of all solutions to the Pell equation `x^2 - d*y^2 = 1`.

The type of such solutions is `Pell.Solution₁ d`. It corresponds to a pair of integers `x` and `y`
and a proof that `(x, y)` is indeed a solution.

The multiplication is given by `(x, y) * (x', y') = (x*x' + d*y*y', x*y' + y*x')`.
This is obtained by mapping `(x, y)` to `x + y*√d` and multiplying the results.
In fact, we define `Pell.Solution₁ d` to be `↥(unitary (ℤ√d))` and transport
the "commutative group with distributive negation" structure from `↥(unitary (ℤ√d))`.

We then set up an API for `Pell.Solution₁ d`.
-/

open CharZero Zsqrtd

theorem is_pell_solution_iff_mem_unitary {d : ℤ} {a : ℤ√d} :
    a.re ^ 2 - d * a.im ^ 2 = 1 ↔ a ∈ unitary (ℤ√d) := by
  rw [← norm_eq_one_iff_mem_unitary, norm_def, sq, sq, ← mul_assoc]

def Solution₁ (d : ℤ) : Type :=
  ↥(unitary (ℤ√d))

namespace Solution₁

variable {d : ℤ}

-- INSTANCE (free from Core): instCommGroup

-- INSTANCE (free from Core): instHasDistribNeg

-- INSTANCE (free from Core): instInhabited

-- INSTANCE (free from Core): :

protected def x (a : Solution₁ d) : ℤ :=
  (a : ℤ√d).re

protected def y (a : Solution₁ d) : ℤ :=
  (a : ℤ√d).im

theorem prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1 :=
  is_pell_solution_iff_mem_unitary.mpr a.property

theorem prop_x (a : Solution₁ d) : a.x ^ 2 = 1 + d * a.y ^ 2 := by rw [← a.prop]; ring

theorem prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 - 1 := by rw [← a.prop]; ring
