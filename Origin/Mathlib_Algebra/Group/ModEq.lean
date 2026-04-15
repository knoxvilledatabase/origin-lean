/-
Extracted from Algebra/Group/ModEq.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equality modulo an element

This file defines equality modulo an element in an additive commutative monoid.
In case of a group, `a` and `b` are congruent modulo `p` iff `b - a ∈ zmultiples p`.

In case of a monoid, the definition is a bit more complicated,
and it is given with the use case of natural numbers in mind.

## Main definitions

* `a ≡ b [PMOD p]`: `a` and `b` are congruent modulo `p`.

## See also

`SModEq` is a generalisation to arbitrary submodules.

## TODO

- Delete `Nat.ModEq` and `Int.ModEq` in favour of `AddCommGroup.ModEq`.
- Relate to `SModEq`.
-/

assert_not_exists Module IsOrderedMonoid Function.support

namespace AddCommGroup

section AddCommMonoid

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

def ModEq (p a b : M) : Prop :=
  ∃ m n : ℕ, m • p + a = n • p + b
