/-
Extracted from Data/Finset/Image.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Image and map operations on finite sets

This file provides the finite analog of `Set.image`, along with some other similar functions.

Note there are two ways to take the image over a finset; via `Finset.image` which applies the
function then removes duplicates (requiring `DecidableEq`), or via `Finset.map` which exploits
injectivity of the function to avoid needing to deduplicate. Choosing between these is similar to
choosing between `insert` and `Finset.cons`, or between `Finset.union` and `Finset.disjUnion`.

## Main definitions

* `Finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `Finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `Finset.filterMap` Given a function `f : α → Option β`, `s.filterMap f` is the
  image finset in `β`, filtering out `none`s.
* `Finset.subtype`: `s.subtype p` is the finset of `Subtype p` whose elements belong to `s`.
* `Finset.fin`:`s.fin n` is the finset of all elements of `s` less than `n`.
-/

assert_not_exists Monoid IsOrderedMonoid

variable {α β γ : Type*}

open Multiset

open Function

namespace Finset

/-! ### map -/

section Map

def map (f : α ↪ β) (s : Finset α) : Finset β :=
  ⟨s.1.map f, s.2.map f.2⟩
