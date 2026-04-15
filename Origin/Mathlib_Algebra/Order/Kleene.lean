/-
Extracted from Algebra/Order/Kleene.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Kleene algebras

This file defines idempotent semirings and Kleene algebras, which are used extensively in the theory
of computation.

An idempotent semiring is a semiring whose addition is idempotent. An idempotent semiring is
naturally a semilattice by setting `a ≤ b` if `a + b = b`.

A Kleene algebra is an idempotent semiring equipped with an additional unary operator `∗`, the
Kleene star, such that (informally) `a∗ = 1 + a + a * a + a * a * a + ...`

## Main declarations

* `IdemSemiring`: Idempotent semiring
* `IdemCommSemiring`: Idempotent commutative semiring
* `KleeneAlgebra`: Kleene algebra

## Notation

`a∗` is notation for `kstar a` in scope `Computability`.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*]
  [kozen1994]
* https://planetmath.org/idempotentsemiring
* https://encyclopediaofmath.org/wiki/Idempotent_semi-ring
* https://planetmath.org/kleene_algebra

## TODO

Instances for `AddOpposite`, `MulOpposite`, `ULift`, `Subsemiring`, `Subring`, `Subalgebra`.

## Tags

kleene algebra, idempotent semiring
-/

open Function

variable {α β ι : Type*} {π : ι → Type*}

class IdemSemiring (α : Type*) extends Semiring α, SemilatticeSup α, OrderBot α where
  protected add_eq_sup (a b : α) : a + b = a ⊔ b := by intros; rfl

class IdemCommSemiring (α : Type*) extends CommSemiring α, IdemSemiring α

class KStar (α : Type*) where
  /-- The Kleene star operator on a Kleene algebra -/
  protected kstar : α → α
