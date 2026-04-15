/-
Extracted from Order/Interval/Finset/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Locally finite orders

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of the
"unbounded" intervals `Ici`/`Ioi` (resp. `Iic`/`Iio`).

Many theorems about these intervals can be found in `Mathlib/Order/Interval/Finset/Basic.lean`.

## Examples

Naturally occurring locally finite orders are `ℕ`, `ℤ`, `ℕ+`, `Fin n`, `α × β` the product of two
locally finite orders, `α →₀ β` the finitely supported functions to a locally finite order `β`...

## Main declarations

In a `LocallyFiniteOrder`,
* `Finset.Icc`: Closed-closed interval as a finset.
* `Finset.Ico`: Closed-open interval as a finset.
* `Finset.Ioc`: Open-closed interval as a finset.
* `Finset.Ioo`: Open-open interval as a finset.
* `Finset.uIcc`: Unordered closed interval as a finset.

In a `LocallyFiniteOrderTop`,
* `Finset.Ici`: Closed-infinite interval as a finset.
* `Finset.Ioi`: Open-infinite interval as a finset.

In a `LocallyFiniteOrderBot`,
* `Finset.Iic`: Infinite-open interval as a finset.
* `Finset.Iio`: Infinite-closed interval as a finset.

## Instances

A `LocallyFiniteOrder` instance can be built
* for a subtype of a locally finite order. See `Subtype.locallyFiniteOrder`.
* for the product of two locally finite orders. See `Prod.locallyFiniteOrder`.
* for any fintype (but not as an instance). See `Fintype.toLocallyFiniteOrder`.
* from a definition of `Finset.Icc` alone. See `LocallyFiniteOrder.ofIcc`.
* by pulling back `LocallyFiniteOrder β` through an order embedding `f : α →o β`. See
  `OrderEmbedding.locallyFiniteOrder`.

Instances for concrete types are proved in their respective files:
* `ℕ` is in `Order.Interval.Finset.Nat`
* `ℤ` is in `Data.Int.Interval`
* `ℕ+` is in `Data.PNat.Interval`
* `Fin n` is in `Order.Interval.Finset.Fin`
* `Finset α` is in `Data.Finset.Interval`
* `Σ i, α i` is in `Data.Sigma.Interval`

Along, you will find lemmas about the cardinality of those finite intervals.

## TODO

Provide the `LocallyFiniteOrder` instance for `α ×ₗ β` where `LocallyFiniteOrder α` and
`Fintype β`.

Provide the `LocallyFiniteOrder` instance for `α →₀ β` where `β` is locally finite. Provide the
`LocallyFiniteOrder` instance for `Π₀ i, β i` where all the `β i` are locally finite.

From `LinearOrder α`, `NoMaxOrder α`, `LocallyFiniteOrder α`, we can also define an
order isomorphism `α ≃ ℕ` or `α ≃ ℤ`, depending on whether we have `OrderBot α` or
`NoMinOrder α` and `Nonempty α`. When `OrderBot α`, we can match `a : α` to `#(Iio a)`.

We can provide `SuccOrder α` from `LinearOrder α` and `LocallyFiniteOrder α` using

```lean
lemma exists_min_greater [LinearOrder α] [LocallyFiniteOrder α] {x ub : α} (hx : x < ub) :
    ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y := by
  -- very non-golfed
  have h : (Finset.Ioc x ub).Nonempty := ⟨ub, Finset.mem_Ioc.2 ⟨hx, le_rfl⟩⟩
  use Finset.min' (Finset.Ioc x ub) h
  constructor
  · exact (Finset.mem_Ioc.mp <| Finset.min'_mem _ h).1
  rintro y hxy
  obtain hy | hy := le_total y ub
  · refine Finset.min'_le (Ioc x ub) y ?_
    simp [*] at *
  · exact (Finset.min'_le _ _ (Finset.mem_Ioc.2 ⟨hx, le_rfl⟩)).trans hy
```
Note that the converse is not true. Consider `{-2^z | z : ℤ} ∪ {2^z | z : ℤ}`. Any element has a
successor (and actually a predecessor as well), so it is a `SuccOrder`, but it's not locally finite
as `Icc (-1) 1` is infinite.
-/

open Finset Function

class LocallyFiniteOrder (α : Type*) [Preorder α] where
  /-- Left-closed right-closed interval -/
  finsetIcc : α → α → Finset α
  /-- Left-closed right-open interval -/
  finsetIco : α → α → Finset α
  /-- Left-open right-closed interval -/
  finsetIoc : α → α → Finset α
  /-- Left-open right-open interval -/
  finsetIoo : α → α → Finset α
  /-- `x ∈ finsetIcc a b ↔ a ≤ x ∧ x ≤ b` -/
  finset_mem_Icc : ∀ a b x : α, x ∈ finsetIcc a b ↔ a ≤ x ∧ x ≤ b
  /-- `x ∈ finsetIco a b ↔ a ≤ x ∧ x < b` -/
  finset_mem_Ico : ∀ a b x : α, x ∈ finsetIco a b ↔ a ≤ x ∧ x < b
  /-- `x ∈ finsetIoc a b ↔ a < x ∧ x ≤ b` -/
  finset_mem_Ioc : ∀ a b x : α, x ∈ finsetIoc a b ↔ a < x ∧ x ≤ b
  /-- `x ∈ finsetIoo a b ↔ a < x ∧ x < b` -/
  finset_mem_Ioo : ∀ a b x : α, x ∈ finsetIoo a b ↔ a < x ∧ x < b
