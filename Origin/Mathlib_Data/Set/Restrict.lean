/-
Extracted from Data/Set/Restrict.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Restrict the domain of a function to a set

## Main definitions

* `Set.restrict f s` : restrict the domain of `f` to the set `s`;
* `Set.codRestrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
-/

variable {α β γ δ : Type*} {ι : Sort*} {π : α → Type*}

open Equiv Equiv.Perm Function

namespace Set

/-! ### Restrict -/

section restrict

def restrict (s : Set α) (f : ∀ a : α, π a) : ∀ a : s, π a := fun x => f x
