/-
Extracted from Algebra/Order/AddTorsor.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ordered scalar multiplication and vector addition
This file defines ordered scalar multiplication and vector addition, and proves some properties.
In the additive case, a motivating example is given by the additive action of `ℤ` on subsets of
reals that are closed under integer translation.  The order compatibility allows for a treatment of
the `R((z))`-module structure on `(z ^ s) V((z))` for an `R`-module `V`, using the formalism of Hahn
series.  In the multiplicative case, a standard example is the action of non-negative rationals on
an ordered field.

## Implementation notes
* Because these classes mix the algebra and order hierarchies, we write them as `Prop`-valued
  mixins.
* Despite the file name, Ordered AddTorsors are not defined as a separate class.  To implement them,
  combine `[AddTorsor G P]` with `[IsOrderedCancelVAdd G P]`

## Definitions
* IsOrderedSMul : inequalities are preserved by scalar multiplication.
* IsOrderedVAdd : inequalities are preserved by translation.
* IsCancelSMul : the scalar multiplication version of cancellative multiplication
* IsCancelVAdd : the vector addition version of cancellative addition
* IsOrderedCancelSMul : inequalities are preserved and reflected by scalar multiplication.
* IsOrderedCancelVAdd : inequalities are preserved and reflected by translation.

## Instances
* OrderedCommMonoid.toIsOrderedSMul
* OrderedAddCommMonoid.toIsOrderedVAdd
* IsOrderedSMul.toCovariantClassLeft
* IsOrderedVAdd.toCovariantClassLeft
* IsOrderedCancelSMul.toCancelSMul
* IsOrderedCancelVAdd.toCancelVAdd
* OrderedCancelCommMonoid.toIsOrderedCancelSMul
* OrderedCancelAddCommMonoid.toIsOrderedCancelVAdd
* IsOrderedCancelSMul.toContravariantClassLeft
* IsOrderedCancelVAdd.toContravariantClassLeft

## TODO
* (lex) prod instances
* Pi instances
* WithTop (in a different file?)
-/

open Function

variable {G P : Type*}

class IsOrderedVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop where
  protected vadd_le_vadd_left : ∀ a b : P, a ≤ b → ∀ c : G, c +ᵥ a ≤ c +ᵥ b
  protected vadd_le_vadd_right : ∀ c d : G, c ≤ d → ∀ a : P, c +ᵥ a ≤ d +ᵥ a
