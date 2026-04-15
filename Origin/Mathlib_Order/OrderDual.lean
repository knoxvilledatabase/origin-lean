/-
Extracted from Order/OrderDual.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Order dual

This file defines `OrderDual α`, a type synonym reversing the meaning of all inequalities,
with notation `αᵒᵈ`.

## Notation

`αᵒᵈ` is notation for `OrderDual α`.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`. Instead, explicit
coercions should be inserted:
* `OrderDual.toDual : α → αᵒᵈ` and `OrderDual.ofDual : αᵒᵈ → α`
-/

assert_not_exists Lex

variable {α : Type*}

def OrderDual (α : Type*) : Type _ :=
  α
