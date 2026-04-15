/-
Extracted from Logic/Function/OfArity.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Function types of a given arity

This provides `Function.OfArity`, such that `OfArity α β 2 = α → α → β`.
Note that it is often preferable to use `(Fin n → α) → β` in place of `OfArity n α β`.

## Main definitions

* `Function.OfArity α β n`: `n`-ary function `α → α → ... → β`. Defined inductively.
* `Function.OfArity.const α b n`: `n`-ary constant function equal to `b`.
-/

universe u

namespace Function

abbrev OfArity (α β : Type u) (n : ℕ) : Type u := FromTypes (fun (_ : Fin n) => α) β
