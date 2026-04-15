/-
Extracted from Order/SymmDiff.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Symmetric difference and bi-implication

This file defines the symmetric difference and bi-implication operators in (co-)Heyting algebras.

## Examples

Some examples are
* The symmetric difference of two sets is the set of elements that are in either but not both.
* The symmetric difference on propositions is `Xor'`.
* The symmetric difference on `Bool` is `Bool.xor`.
* The equivalence of propositions. Two propositions are equivalent if they imply each other.
* The symmetric difference translates to addition when considering a Boolean algebra as a Boolean
  ring.

## Main declarations

* `symmDiff`: The symmetric difference operator, defined as `(a \ b) ⊔ (b \ a)`
* `bihimp`: The bi-implication operator, defined as `(b ⇨ a) ⊓ (a ⇨ b)`

In generalized Boolean algebras, the symmetric difference operator is:

* `symmDiff_comm`: commutative, and
* `symmDiff_assoc`: associative.

## Notation

* `a ∆ b`: `symmDiff a b`
* `a ⇔ b`: `bihimp a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags

boolean ring, generalized boolean algebra, boolean algebra, symmetric difference, bi-implication,
Heyting
-/

assert_not_exists RelIso

open Function OrderDual

variable {ι α β : Type*} {π : ι → Type*}

def symmDiff [Max α] [SDiff α] (a b : α) : α :=
  a \ b ⊔ b \ a

def bihimp [Min α] [HImp α] (a b : α) : α :=
  (b ⇨ a) ⊓ (a ⇨ b)

scoped[symmDiff] infixl:100 " ∆ " => symmDiff

scoped[symmDiff] infixl:100 " ⇔ " => bihimp

open scoped symmDiff
