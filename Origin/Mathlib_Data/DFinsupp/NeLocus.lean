/-
Extracted from Data/DFinsupp/NeLocus.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Locus of unequal values of finitely supported dependent functions

Let `N : α → Type*` be a type family, assume that `N a` has a `0` for all `a : α` and let
`f g : Π₀ a, N a` be finitely supported dependent functions.

## Main definition

* `DFinsupp.neLocus f g : Finset α`, the finite subset of `α` where `f` and `g` differ.
  In the case in which `N a` is an additive group for all `a`, `DFinsupp.neLocus f g` coincides with
  `DFinsupp.support (f - g)`.
-/

variable {α : Type*} {N : α → Type*}

namespace DFinsupp

variable [DecidableEq α]

section NHasZero

variable [∀ a, DecidableEq (N a)] [∀ a, Zero (N a)] (f g : Π₀ a, N a)

def neLocus (f g : Π₀ a, N a) : Finset α :=
  (f.support ∪ g.support).filter fun x ↦ f x ≠ g x
