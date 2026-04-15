/-
Extracted from Order/Interval/Multiset.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Intervals as multisets

This file defines intervals as multisets.

## Main declarations

In a `LocallyFiniteOrder`,
* `Multiset.Icc`: Closed-closed interval as a multiset.
* `Multiset.Ico`: Closed-open interval as a multiset.
* `Multiset.Ioc`: Open-closed interval as a multiset.
* `Multiset.Ioo`: Open-open interval as a multiset.

In a `LocallyFiniteOrderTop`,
* `Multiset.Ici`: Closed-infinite interval as a multiset.
* `Multiset.Ioi`: Open-infinite interval as a multiset.

In a `LocallyFiniteOrderBot`,
* `Multiset.Iic`: Infinite-open interval as a multiset.
* `Multiset.Iio`: Infinite-closed interval as a multiset.

## TODO

Do we really need this file at all? (March 2024)
-/

variable {α : Type*}

namespace Multiset

section LocallyFiniteOrder

variable [Preorder α] [LocallyFiniteOrder α] {a b x : α}

def Icc (a b : α) : Multiset α := (Finset.Icc a b).val

def Ico (a b : α) : Multiset α := (Finset.Ico a b).val

def Ioc (a b : α) : Multiset α := (Finset.Ioc a b).val

def Ioo (a b : α) : Multiset α := (Finset.Ioo a b).val
