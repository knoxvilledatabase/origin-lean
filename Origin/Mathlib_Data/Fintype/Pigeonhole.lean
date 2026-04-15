/-
Extracted from Data/Fintype/Pigeonhole.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pigeonhole principles in finite types

## Main declarations

We provide the following versions of the pigeonholes principle.
* `Fintype.exists_ne_map_eq_of_card_lt` and `isEmpty_of_card_lt`: Finitely many pigeons and
  pigeonholes. Weak formulation.
* `Finite.exists_ne_map_eq_of_infinite`: Infinitely many pigeons in finitely many pigeonholes.
  Weak formulation.
* `Finite.exists_infinite_fiber`: Infinitely many pigeons in finitely many pigeonholes. Strong
  formulation.

Some more pigeonhole-like statements can be found in `Data.Fintype.CardEmbedding`.
-/

assert_not_exists MonoidWithZero MulAction

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

variable [Fintype α] [Fintype β]

theorem exists_ne_map_eq_of_card_lt (f : α → β) (h : Fintype.card β < Fintype.card α) :
    ∃ x y, x ≠ y ∧ f x = f y :=
  let ⟨x, _, y, _, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h fun x _ => mem_univ (f x)
  ⟨x, y, h⟩

end Fintype

namespace Function.Embedding
