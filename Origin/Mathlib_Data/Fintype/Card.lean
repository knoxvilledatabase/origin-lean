/-
Extracted from Data/Fintype/Card.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cardinalities of finite types

This file defines the cardinality `Fintype.card α` as the number of elements in `(univ : Finset α)`.
We also include some elementary results on the values of `Fintype.card` on specific types.

## Main declarations

* `Fintype.card α`: Cardinality of a fintype. Equal to `Finset.univ.card`.
* `Finite.surjective_of_injective`: an injective function from a finite type to
  itself is also surjective.

-/

assert_not_exists Monoid

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

def card (α) [Fintype α] : ℕ :=
  (@univ α _).card

theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    @card { x // p x } (Fintype.subtype s H) = #s :=
  Multiset.card_pmap _ _ _

theorem card_of_subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x)
    [Fintype { x // p x }] : card { x // p x } = #s := by
  rw [← subtype_card s H]
  congr!
