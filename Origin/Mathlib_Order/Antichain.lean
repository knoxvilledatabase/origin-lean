/-
Extracted from Order/Antichain.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Antichains

This file defines antichains. An antichain is a set where any two distinct elements are not related.
If the relation is `(≤)`, this corresponds to incomparability and usual order antichains. If the
relation is `G.Adj` for `G : SimpleGraph α`, this corresponds to independent sets of `G`.

## Definitions

* `IsAntichain r s`: Any two elements of `s : Set α` are unrelated by `r : α → α → Prop`.
* `IsStrongAntichain r s`: Any two elements of `s : Set α` are not related by `r : α → α → Prop`
  to a common element.
* `IsMaxAntichain r s`: An antichain such that no antichain strictly including `s` exists.
-/

assert_not_exists CompleteLattice

open Function Set Set.Notation

section General

variable {α β : Type*} {r r₁ r₂ : α → α → Prop} {r' : β → β → Prop} {s t : Set α} {a b : α}

protected theorem Symmetric.compl (h : Symmetric r) : Symmetric rᶜ := fun _ _ hr hr' =>
  hr <| h hr'

def IsAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  s.Pairwise rᶜ

namespace IsAntichain
