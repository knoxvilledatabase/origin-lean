/-
Extracted from Data/SetLike/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Typeclass for types with a set-like extensionality property

The `Membership` typeclass is used to let terms of a type have elements.
Many instances of `Membership` have a set-like extensionality property:
things are equal iff they have the same elements.  The `SetLike`
typeclass provides a unified interface to define a `Membership` that is
extensional in this way.

The main use of `SetLike` is for algebraic subobjects (such as
`Submonoid` and `Submodule`), whose non-proof data consists only of a
carrier set.  In such a situation, the projection to the carrier set
is injective.

In general, a type `A` is `SetLike` with elements of type `B` if it
has an injective map to `Set B`.  This module provides standard
boilerplate for every `SetLike`: a `coe_sort`, a `coe` to set,
and various extensionality and simp lemmas. The order induced by set inclusion is
called `PartialOrder.ofSetlike`: this is not an instance for flexibility in choosing orders.
The class `IsConcreteLE` abstractly states the order is equal to that induced by set inclusion;
an instance is automatically available when defining a `PartialOrder` as
`.ofSetLike (MySubobject X) X`.

A typical subobject should be declared as:
```
structure MySubobject (X : Type*) [ObjectTypeclass X] where
  (carrier : Set X)
  (op_mem' : ∀ {x : X}, x ∈ carrier → sorry ∈ carrier)

namespace MySubobject

variable {X : Type*} [ObjectTypeclass X] {x : X}

instance : SetLike (MySubobject X) X :=
  ⟨MySubobject.carrier, fun p q h => by cases p; cases q; congr!⟩

instance : PartialOrder (MySubobject X) := .ofSetLike (MySubobject X) X

@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl

@[ext] theorem ext {p q : MySubobject X} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

/-- Copy of a `MySubobject` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/

protected def copy (p : MySubobject X) (s : Set X) (hs : s = ↑p) : MySubobject X :=
  { carrier := s
    op_mem' := hs.symm ▸ p.op_mem' }
