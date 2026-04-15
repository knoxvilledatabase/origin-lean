/-
Extracted from Data/Finset/Prod.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Finsets in product types

This file defines finset constructions on the product type `α × β`. Beware not to confuse with the
`Finset.prod` operation which computes the multiplicative product.

## Main declarations

* `Finset.product`: Turns `s : Finset α`, `t : Finset β` into their product in `Finset (α × β)`.
* `Finset.diag`: For `s : Finset α`, `s.diag` is the `Finset (α × α)` of pairs `(a, a)` with
  `a ∈ s`.
* `Finset.offDiag`: For `s : Finset α`, `s.offDiag` is the `Finset (α × α)` of pairs `(a, b)` with
  `a, b ∈ s` and `a ≠ b`.
-/

assert_not_exists MonoidWithZero

open Multiset

variable {α β γ : Type*}

namespace Finset

/-! ### prod -/

section Prod

variable {s s' : Finset α} {t t' : Finset β} {a : α} {b : β}

protected def product (s : Finset α) (t : Finset β) : Finset (α × β) :=
  ⟨_, s.nodup.product t.nodup⟩

-- INSTANCE (free from Core): instSProd
