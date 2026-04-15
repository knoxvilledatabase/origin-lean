/-
Extracted from Data/W/Basic.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# W types

Given `α : Type` and `β : α → Type`, the W type determined by this data, `WType β`, is the
inductively defined type of trees where the nodes are labeled by elements of `α` and the children of
a node labeled `a` are indexed by elements of `β a`.

This file is currently a stub, awaiting a full development of the theory. Currently, the main result
is that if `α` is an encodable fintype and `β a` is encodable for every `a : α`, then `WType β` is
encodable. This can be used to show the encodability of other inductive types, such as those that
are commonly used to formalize syntax, e.g. terms and expressions in a given language. The strategy
is illustrated in the example found in the file `prop_encodable` in the `archive/examples` folder of
mathlib.

## Implementation details

While the name `WType` is somewhat verbose, it is preferable to putting a single character
identifier `W` in the root namespace.
-/

inductive WType {α : Type*} (β : α → Type*)
  | mk (a : α) (f : β a → WType β) : WType β

-- INSTANCE (free from Core): :

namespace WType

variable {α : Type*} {β : α → Type*}

def toSigma : WType β → Σ a : α, β a → WType β
  | ⟨a, f⟩ => ⟨a, f⟩

def ofSigma : (Σ a : α, β a → WType β) → WType β
  | ⟨a, f⟩ => WType.mk a f
