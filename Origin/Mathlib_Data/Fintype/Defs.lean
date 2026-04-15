/-
Extracted from Data/Fintype/Defs.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Finite types

This file defines a typeclass to state that a type is finite.

## Main declarations

* `Fintype α`:  Typeclass saying that a type is finite. It takes as fields a `Finset` and a proof
  that all terms of type `α` are in it.
* `Finset.univ`: The finset of all elements of a fintype.

See `Data.Fintype.Basic` for elementary results,
`Data.Fintype.Card` for the cardinality of a fintype,
the equivalence with `Fin (Fintype.card α)`, and pigeonhole principles.

## Instances

Instances for `Fintype` for
* `{x // p x}` are in this file as `Fintype.subtype`
* `Option α` are in `Data.Fintype.Option`
* `α × β` are in `Data.Fintype.Prod`
* `α ⊕ β` are in `Data.Fintype.Sum`
* `Σ (a : α), β a` are in `Data.Fintype.Sigma`

These files also contain appropriate `Infinite` instances for these types.

`Infinite` instances for `ℕ`, `ℤ`, `Multiset α`, and `List α` are in `Data.Fintype.Lattice`.
-/

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

class Fintype (α : Type*) where
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : Finset α
  /-- A proof that `elems` contains every element of the type -/
  complete : ∀ x : α, x ∈ elems

/-! ### Preparatory lemmas -/

namespace Finset

theorem nodup_map_iff_injOn {f : α → β} {s : Finset α} :
    (Multiset.map f s.val).Nodup ↔ Set.InjOn f s := by
  simp [Multiset.nodup_map_iff_inj_on s.nodup, Set.InjOn]

end Finset

namespace List

variable [DecidableEq α] {a : α} {f : α → β} {s : Finset α} {t : Set β} {t' : Finset β}

-- INSTANCE (free from Core): [DecidableEq

-- INSTANCE (free from Core): [DecidableEq

end List

namespace Finset

variable [Fintype α] {s t : Finset α}

def univ : Finset α :=
  @Fintype.elems α _
