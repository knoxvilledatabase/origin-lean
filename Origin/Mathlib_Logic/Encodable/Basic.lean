/-
Extracted from Logic/Encodable/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Encodable types

This file defines encodable (constructively countable) types as a typeclass.
This is used to provide explicit encode/decode functions from and to `ℕ`, with the information that
those functions are inverses of each other.
The difference with `Denumerable` is that finite types are encodable. For infinite types,
`Encodable` and `Denumerable` agree.

## Main declarations

* `Encodable α`: States that there exists an explicit encoding function `encode : α → ℕ` with a
  partial inverse `decode : ℕ → Option α`.
* `decode₂`: Version of `decode` that is equal to `none` outside of the range of `encode`. Useful as
  we do not require this in the definition of `decode`.
* `ULower α`: Any encodable type has an equivalent type living in the lowest universe, namely a
  subtype of `ℕ`. `ULower α` finds it.

## Implementation notes

The point of asking for an explicit partial inverse `decode : ℕ → Option α` to `encode : α → ℕ` is
to make the range of `encode` decidable even when the finiteness of `α` is not.
-/

assert_not_exists Monoid

set_option linter.unusedDecidableInType false

open Option List Nat Function

class Encodable (α : Type*) where
  /-- Encoding from Type α to ℕ -/
  encode : α → ℕ
  /-- Decoding from ℕ to Option α -/
  decode : ℕ → Option α
  /-- Invariant relationship between encoding and decoding -/
  encodek : ∀ a, decode (encode a) = some a

attribute [simp] Encodable.encodek

namespace Encodable

variable {α : Type*} {β : Type*}

universe u

theorem encode_injective [Encodable α] : Function.Injective (@encode α _)
  | x, y, e => Option.some.inj <| by rw [← encodek, e, encodek]
