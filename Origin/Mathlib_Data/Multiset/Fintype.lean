/-
Extracted from Data/Multiset/Fintype.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Multiset coercion to type

This module defines a `CoeSort` instance for multisets and gives it a `Fintype` instance.
It also defines `Multiset.toEnumFinset`, which is another way to enumerate the elements of
a multiset. These coercions and definitions make it easier to sum over multisets using existing
`Finset` theory.

## Main definitions

* A coercion from `m : Multiset α` to a `Type*`. Each `x : m` has two components.
  The first, `x.1`, can be obtained via the coercion `↑x : α`,
  and it yields the underlying element of the multiset.
  The second, `x.2`, is a term of `Fin (m.count x)`,
  and its function is to ensure each term appears with the correct multiplicity.
  Note that this coercion requires `DecidableEq α` due to the definition using `Multiset.count`.
* `Multiset.toEnumFinset` is a `Finset` version of this.
* `Multiset.coeEmbedding` is the embedding `m ↪ α × ℕ`, whose first component is the coercion
  and whose second component enumerates elements with multiplicity.
* `Multiset.coeEquiv` is the equivalence `m ≃ m.toEnumFinset`.

## Tags

multiset enumeration
-/

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {m : Multiset α}

namespace Multiset

def ToType (m : Multiset α) : Type _ := (x : α) × Fin (m.count x)

-- INSTANCE (free from Core): :

example : DecidableEq m := inferInstanceAs <| DecidableEq ((x : α) × Fin (m.count x))
