/-
Extracted from Logic/Denumerable.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Denumerable types

This file defines denumerable (countably infinite) types as a typeclass extending `Encodable`. This
is used to provide explicit encode/decode functions from and to `ℕ`, with the information that those
functions are inverses of each other.

## Implementation notes

This property already has a name, namely `α ≃ ℕ`, but here we are interested in using it as a
typeclass.
-/

assert_not_exists Monoid

variable {α β : Type*}

class Denumerable (α : Type*) extends Encodable α where
  /-- `decode` and `encode` are inverses. -/
  decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n

open Finset Nat

namespace Denumerable

variable [Denumerable α] [Denumerable β]

open Encodable

theorem decode_isSome (α) [Denumerable α] (n : ℕ) : (decode (α := α) n).isSome :=
  Option.isSome_iff_exists.2 <| (decode_inv n).imp fun _ => And.left

def ofNat (α) [Denumerable α] (n : ℕ) : α :=
  Option.get _ (decode_isSome α n)
