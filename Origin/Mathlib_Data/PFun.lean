/-
Extracted from Data/PFun.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Partial functions

This file defines partial functions. Partial functions are like functions, except they can also be
"undefined" on some inputs. We define them as functions `α → Part β`.

## Definitions

* `PFun α β`: Type of partial functions from `α` to `β`. Defined as `α → Part β` and denoted
  `α →. β`.
* `PFun.Dom`: Domain of a partial function. Set of values on which it is defined. Not to be confused
  with the domain of a function `α → β`, which is a type (`α` presently).
* `PFun.fn`: Evaluation of a partial function. Takes in an element and a proof it belongs to the
  partial function's `Dom`.
* `PFun.asSubtype`: Returns a partial function as a function from its `Dom`.
* `PFun.toSubtype`: Restricts the codomain of a function to a subtype.
* `PFun.evalOpt`: Returns a partial function with a decidable `Dom` as a function `a → Option β`.
* `PFun.lift`: Turns a function into a partial function.
* `PFun.id`: The identity as a partial function.
* `PFun.comp`: Composition of partial functions.
* `PFun.restrict`: Restriction of a partial function to a smaller `Dom`.
* `PFun.res`: Turns a function into a partial function with a prescribed domain.
* `PFun.fix` : First return map of a partial function `f : α →. β ⊕ α`.
* `PFun.fixInduction`: A recursion principle for `PFun.fix`.

### Partial functions as relations

Partial functions can be considered as relations, so we specialize some `Rel` definitions to `PFun`:
* `PFun.image`: Image of a set under a partial function.
* `PFun.ran`: Range of a partial function.
* `PFun.preimage`: Preimage of a set under a partial function.
* `PFun.core`: Core of a set under a partial function.
* `PFun.graph`: Graph of a partial function `a →. β` as a `Set (α × β)`.
* `PFun.graph'`: Graph of a partial function `a →. β` as a `Rel α β`.

### `PFun α` as a monad

Monad operations:
* `PFun.pure`: The monad `pure` function, the constant `x` function.
* `PFun.bind`: The monad `bind` function, pointwise `Part.bind`
* `PFun.map`: The monad `map` function, pointwise `Part.map`.
-/

open Function

def PFun (α β : Type*) :=
  α → Part β

infixr:25 " →. " => PFun

namespace PFun

variable {α β γ δ ε ι : Type*}

-- INSTANCE (free from Core): inhabited

def Dom (f : α →. β) : Set α :=
  {a | (f a).Dom}
