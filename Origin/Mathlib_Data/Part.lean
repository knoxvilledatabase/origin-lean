/-
Extracted from Data/Part.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Partial values of a type
This file defines `Part α`, the partial values of a type.
`o : Part α` carries a proposition `o.Dom`, its domain, along with a function `get : o.Dom → α`, its
value. The rule is then that every partial value has a value but, to access it, you need to provide
a proof of the domain.
`Part α` behaves the same as `Option α` except that `o : Option α` is decidably `none` or `some a`
for some `a : α`, while the domain of `o : Part α` doesn't have to be decidable. That means you can
translate back and forth between a partial value with a decidable domain and an option, and
`Option α` and `Part α` are classically equivalent. In general, `Part α` is bigger than `Option α`.

## Main declarations
`Option`-like declarations:
* `Part.none`: The partial value whose domain is `False`.
* `Part.some a`: The partial value whose domain is `True` and whose value is `a`.
* `Part.ofOption`: Converts an `Option α` to a `Part α` by sending `none` to `none` and `some a` to
  `some a`.
* `Part.toOption`: Converts a `Part α` with a decidable domain to an `Option α`.
* `Part.equivOption`: Classical equivalence between `Part α` and `Option α`.
Monadic structure:
* `Part.bind`: `o.bind f` has value `(f (o.get _)).get _` (`f o` morally) and is defined when `o`
  and `f (o.get _)` are defined.
* `Part.map`: Maps the value and keeps the same domain.
Other:
* `Part.restrict`: `Part.restrict p o` replaces the domain of `o : Part α` by `p : Prop` so long as
  `p → o.Dom`.
* `Part.assert`: `assert p f` appends `p` to the domains of the values of a partial function.
* `Part.unwrap`: Gets the value of a partial value regardless of its domain. Unsound.
## Notation
For `a : α`, `o : Part α`, `a ∈ o` means that `o` is defined and equal to `a`. Formally, it means
`o.Dom` and `o.get _ = a`.
-/

assert_not_exists RelIso

open Function

structure Part.{u} (α : Type u) : Type u where
  /-- The domain of a partial value -/
  Dom : Prop
  /-- Extract a value from a partial value given a proof of `Dom` -/
  get : Dom → α

namespace Part

variable {α : Type*} {β : Type*} {γ : Type*}

def toOption (o : Part α) [Decidable o.Dom] : Option α :=
  if h : Dom o then some (o.get h) else none
