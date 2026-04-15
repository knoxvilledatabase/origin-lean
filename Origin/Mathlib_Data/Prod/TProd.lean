/-
Extracted from Data/Prod/TProd.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Finite products of types

This file defines the product of types over a list. For `l : List ι` and `α : ι → Type v` we define
`List.TProd α l = l.foldr (fun i β ↦ α i × β) PUnit`.
This type should not be used if `∀ i, α i` or `∀ i ∈ l, α i` can be used instead
(in the last expression, we could also replace the list `l` by a set or a finset).
This type is used as an intermediary between binary products and finitary products.
The application of this type is finitary product measures, but it could be used in any
construction/theorem that is easier to define/prove on binary products than on finitary products.

* Once we have the construction on binary products (like binary product measures in
  `MeasureTheory.prod`), we can easily define a finitary version on the type `TProd l α`
  by iterating. Properties can also be easily extended from the binary case to the finitary case
  by iterating.
* Then we can use the equivalence `List.TProd.piEquivTProd` below (or enhanced versions of it,
  like a `MeasurableEquiv` for product measures) to get the construction on `∀ i : ι, α i`, at
  least when assuming `[Fintype ι] [Encodable ι]` (using `Encodable.sortedUniv`).
  Using `attribute [local instance] Fintype.toEncodable` we can get rid of the argument
  `[Encodable ι]`.

## Main definitions

* We have the equivalence `TProd.piEquivTProd : (∀ i, α i) ≃ TProd α l`
  if `l` contains every element of `ι` exactly once.
* The product of sets is `Set.tprod : (∀ i, Set (α i)) → Set (TProd α l)`.
-/

open List Function

universe u v

variable {ι : Type u} {α : ι → Type v} {i j : ι} {l : List ι}

namespace List

variable (α) in

abbrev TProd (l : List ι) : Type v :=
  l.foldr (fun i β => α i × β) PUnit

namespace TProd

protected def mk : ∀ (l : List ι) (_f : ∀ i, α i), TProd α l
  | [] => fun _ => PUnit.unit
  | i :: is => fun f => (f i, TProd.mk is f)

-- INSTANCE (free from Core): [∀
