/-
Extracted from Data/Finsupp/Single.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finitely supported functions on exactly one point

This file contains definitions and basic results on defining/updating/removing `Finsupp`s
using one point of the domain.

## Main declarations

* `Finsupp.single`: The `Finsupp` which is nonzero in exactly one point.
* `Finsupp.update`: Changes one value of a `Finsupp`.
* `Finsupp.erase`: Replaces one value of a `Finsupp` by `0`.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.
-/

assert_not_exists CompleteLattice

noncomputable section

open Finset Function

variable {α β γ ι M M' N P G H R S : Type*}

namespace Finsupp

/-! ### Declarations about `single` -/

section Single

variable [Zero M] {a a' : α} {b : M}

def single (a : α) (b : M) : α →₀ M where
  support :=
    haveI := Classical.decEq M
    if b = 0 then ∅ else {a}
  toFun :=
    haveI := Classical.decEq α
    Pi.single a b
  mem_support_toFun a' := by grind
