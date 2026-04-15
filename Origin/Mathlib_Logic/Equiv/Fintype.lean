/-
Extracted from Logic/Equiv/Fintype.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Equivalence between fintypes

This file contains some basic results on equivalences where one or both
sides of the equivalence are `Fintype`s.

## Main definitions

- `Function.Embedding.toEquivRange`: computably turn an embedding of a
  fintype into an `Equiv` of the domain to its range
- `Equiv.Perm.viaFintypeEmbedding : Perm α → (α ↪ β) → Perm β` extends the domain of
  a permutation, fixing everything outside the range of the embedding

## Implementation details

- `Function.Embedding.toEquivRange` uses a computable inverse, but one that has poor
  computational performance, since it operates by exhaustive search over the input `Fintype`s.
-/

assert_not_exists Equiv.Perm.sign

section Fintype

variable {α β : Type*} [Fintype α] [DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β)

def Function.Embedding.toEquivRange : α ≃ Set.range f where
  toFun := fun a => ⟨f a, Set.mem_range_self a⟩
  invFun := f.invOfMemRange
  left_inv := fun _ => by simp
  right_inv := fun _ => by simp
