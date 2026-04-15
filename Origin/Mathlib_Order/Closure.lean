/-
Extracted from Order/Closure.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Closure operators between preorders

We define (bundled) closure operators on a preorder as monotone (increasing), extensive
(inflationary) and idempotent functions.
We define closed elements for the operator as elements which are fixed by it.

Lower adjoints to a function between preorders `u : β → α` allow to generalise closure operators to
situations where the closure operator we are dealing with naturally decomposes as `u ∘ l` where `l`
is a worthy function to have on its own. Typical examples include
`l : Set G → Subgroup G := Subgroup.closure`, `u : Subgroup G → Set G := (↑)`, where `G` is a group.
This shows there is a close connection between closure operators, lower adjoints and Galois
connections/insertions: every Galois connection induces a lower adjoint which itself induces a
closure operator by composition (see `GaloisConnection.lowerAdjoint` and
`LowerAdjoint.closureOperator`), and every closure operator on a partial order induces a Galois
insertion from the set of closed elements to the underlying type (see `ClosureOperator.gi`).

## Main definitions

* `ClosureOperator`: A closure operator is a monotone function `f : α → α` such that
  `∀ x, x ≤ f x` and `∀ x, f (f x) = f x`.
* `LowerAdjoint`: A lower adjoint to `u : β → α` is a function `l : α → β` such that `l` and `u`
  form a Galois connection.

## Implementation details

Although `LowerAdjoint` is technically a generalisation of `ClosureOperator` (by defining
`toFun := id`), it is desirable to have both as otherwise `id`s would be carried all over the
place when using concrete closure operators such as `ConvexHull`.

`LowerAdjoint` really is a semibundled `structure` version of `GaloisConnection`.

## References

* https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets
-/

open Set

/-! ### Closure operator -/

variable (α : Type*) {ι : Sort*} {κ : ι → Sort*}

structure ClosureOperator [Preorder α] extends α →o α where
  /-- An element is less than or equal its closure -/
  le_closure' : ∀ x, x ≤ toFun x
  /-- Closures are idempotent -/
  idempotent' : ∀ x, toFun (toFun x) = toFun x
  /-- Predicate for an element to be closed.

  By default, this is defined as `c.IsClosed x := (c x = x)` (see `isClosed_iff`).
  We allow an override to fix definitional equalities. -/
  IsClosed (x : α) : Prop := toFun x = x
  isClosed_iff {x : α} : IsClosed x ↔ toFun x = x := by aesop

namespace ClosureOperator

-- INSTANCE (free from Core): [Preorder

-- INSTANCE (free from Core): [Preorder

initialize_simps_projections ClosureOperator (toFun → apply, IsClosed → isClosed)
