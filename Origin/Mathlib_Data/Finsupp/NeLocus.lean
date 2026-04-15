/-
Extracted from Data/Finsupp/NeLocus.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Locus of unequal values of finitely supported functions

Let `α N` be two Types, assume that `N` has a `0` and let `f g : α →₀ N` be finitely supported
functions.

## Main definition

* `Finsupp.neLocus f g : Finset α`, the finite subset of `α` where `f` and `g` differ.

In the case in which `N` is an additive group, `Finsupp.neLocus f g` coincides with
`Finsupp.support (f - g)`.
-/

variable {α M N P : Type*}

namespace Finsupp

variable [DecidableEq α]

section NHasZero

variable [DecidableEq N] [Zero N] (f g : α →₀ N)

def neLocus (f g : α →₀ N) : Finset α :=
  (f.support ∪ g.support).filter fun x => f x ≠ g x
