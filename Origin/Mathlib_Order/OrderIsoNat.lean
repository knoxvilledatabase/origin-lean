/-
Extracted from Order/OrderIsoNat.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relation embeddings from the naturals

This file allows translation from monotone functions `ℕ → α` to order embeddings `ℕ ↪ α` and
defines the limit value of an eventually-constant sequence.

## Main declarations

* `natLT`/`natGT`: Make an order embedding `Nat ↪ α` from
  an increasing/decreasing function `Nat → α`.
* `monotonicSequenceLimit`: The limit of an eventually-constant monotone sequence `Nat →o α`.
* `monotonicSequenceLimitIndex`: The index of the first occurrence of `monotonicSequenceLimit`
  in the sequence.
-/

variable {α : Type*}

namespace RelEmbedding

variable {r : α → α → Prop} [IsStrictOrder α r]

def natLT (f : ℕ → α) (H : ∀ n : ℕ, r (f n) (f (n + 1))) : ((· < ·) : ℕ → ℕ → Prop) ↪r r :=
  ofMonotone f <| Nat.rel_of_forall_rel_succ_of_lt r H
