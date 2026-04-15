/-
Extracted from Data/List/Sigma.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Utilities for lists of sigmas

This file includes several ways of interacting with `List (Sigma β)`, treated as a key-value store.

If `α : Type*` and `β : α → Type*`, then we regard `s : Sigma β` as having key `s.1 : α` and value
`s.2 : β s.1`. Hence, `List (Sigma β)` behaves like a key-value store.

## Main Definitions

- `List.keys` extracts the list of keys.
- `List.NodupKeys` determines if the store has duplicate keys.
- `List.lookup`/`lookup_all` accesses the value(s) of a particular key.
- `List.kreplace` replaces the first value with a given key by a given value.
- `List.kerase` removes a value.
- `List.kinsert` inserts a value.
- `List.kunion` computes the union of two stores.
- `List.kextract` returns a value with a given key and the rest of the values.
-/

universe u u' v v'

namespace List

variable {α : Type u} {α' : Type u'} {β : α → Type v} {β' : α' → Type v'} {l l₁ l₂ : List (Sigma β)}

/-! ### `keys` -/

def keys : List (Sigma β) → List α :=
  map Sigma.fst
