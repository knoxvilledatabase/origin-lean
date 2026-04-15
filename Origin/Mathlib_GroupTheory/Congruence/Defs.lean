/-
Extracted from GroupTheory/Congruence/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Congruence relations

This file defines congruence relations: equivalence relations that preserve a binary operation,
which in this case is multiplication or addition. The principal definition is a `structure`
extending a `Setoid` (an equivalence relation), and the inductive definition of the smallest
congruence relation containing a binary relation is also given (see `ConGen`).

The file also proves basic properties of the quotient of a type by a congruence relation, and the
complete lattice of congruence relations on a type. We then establish an order-preserving bijection
between the set of congruence relations containing a congruence relation `c` and the set of
congruence relations on the quotient by `c`.

The second half of the file concerns congruence relations on monoids, in which case the
quotient by the congruence relation is also a monoid.

## Implementation notes

The inductive definition of a congruence relation could be a nested inductive type, defined using
the equivalence closure of a binary relation `EqvGen`, but the recursor generated does not work.
A nested inductive definition could conceivably shorten proofs, because they would allow invocation
of the corresponding lemmas about `EqvGen`.

The lemmas `refl`, `symm` and `trans` are not tagged with `@[refl]`, `@[symm]`, and `@[trans]`
respectively as these tags do not work on a structure coerced to a binary relation.

There is a coercion from elements of a type to the element's equivalence class under a
congruence relation.

A congruence relation on a monoid `M` can be thought of as a submonoid of `M × M` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid, isomorphism theorems
-/

variable (M : Type*) {N : Type*} {P : Type*}

open Function Setoid

structure AddCon [Add M] extends Setoid M where
  /-- Additive congruence relations are closed under addition -/
  add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z)
