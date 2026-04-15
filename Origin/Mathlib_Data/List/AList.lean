/-
Extracted from Data/List/AList.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Association Lists

This file defines association lists. An association list is a list where every element consists of
a key and a value, and no two entries have the same key. The type of the value is allowed to be
dependent on the type of the key.

This type dependence is implemented using `Sigma`: The elements of the list are of type `Sigma β`,
for some type index `β`.

## Main definitions

Association lists are represented by the `AList` structure. This file defines this structure and
provides ways to access, modify, and combine `AList`s.

* `AList.keys` returns a list of keys of the alist.
* `AList.membership` returns membership in the set of keys.
* `AList.erase` removes a certain key.
* `AList.insert` adds a key-value mapping to the list.
* `AList.union` combines two association lists.

## References

* <https://en.wikipedia.org/wiki/Association_list>

-/

universe u v w

open List

variable {α : Type u} {β : α → Type v}

structure AList (β : α → Type v) : Type max u v where
  /-- The underlying `List` of an `AList` -/
  entries : List (Sigma β)
  /-- There are no duplicate keys in `entries` -/
  nodupKeys : entries.NodupKeys

def List.toAList [DecidableEq α] {β : α → Type v} (l : List (Sigma β)) : AList β where
  entries := _
  nodupKeys := nodupKeys_dedupKeys l

namespace AList
