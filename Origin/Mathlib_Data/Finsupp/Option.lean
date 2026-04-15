/-
Extracted from Data/Finsupp/Option.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Operations on `Finsupp`s with an `Option` domain

Similar to how `Finsupp.cons` and `Finsupp.tail` construct
an object of type `Fin (n + 1) →₀ M` from a map `Fin n →₀ M` and vice versa,
we define `Finsupp.optionElim` and `Finsupp.some`
to construct `Option α →₀ M` from a map α →₀ M, and vice versa.

As functions, these behave as `Option.elim'`, and as an application of `some` hence the names.

We prove a variety of API lemmas, see `Mathlib/Data/Finsupp/Fin.lean` for comparison.

## Main declarations

* `Finsupp.some`: restrict a finitely supported function on `Option α` to a finitely supported
  function on `α`.
* `Finsupp.optionElim`: extend a finitely supported function on `α`
  to a finitely supported function on `Option α`, provided a default value for `none`.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

-/

noncomputable section

open Finset Function

variable {α M N R : Type*}

namespace Finsupp

section Option

section Zero

variable [Zero M]

def some (f : Option α →₀ M) : α →₀ M :=
  f.comapDomain Option.some fun _ => by simp
