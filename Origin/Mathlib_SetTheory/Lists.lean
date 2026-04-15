/-
Extracted from SetTheory/Lists.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# A computable model of ZFA without infinity

In this file we define finite hereditary lists. This is useful for calculations in naive set theory.

We distinguish two kinds of ZFA lists:
* Atoms. Directly correspond to an element of the original type.
* Proper ZFA lists. Can be thought of (but are not implemented) as a list of ZFA lists (not
  necessarily proper).

For example, `Lists ℕ` contains stuff like `23`, `[]`, `[37]`, `[1, [[2], 3], 4]`.

## Implementation note

As we want to be able to append both atoms and proper ZFA lists to proper ZFA lists, it's handy that
atoms and proper ZFA lists belong to the same type, even though atoms of `α` could be modelled as
`α` directly. But we don't want to be able to append anything to atoms.

This calls for a two-step definition of ZFA lists:
* First, define ZFA prelists as atoms and proper ZFA prelists. Those proper ZFA prelists are defined
  by inductive appending of (not necessarily proper) ZFA lists.
* Second, define ZFA lists by rubbing out the distinction between atoms and proper lists.

## Main declarations

* `Lists' α false`: Atoms as ZFA prelists. Basically a copy of `α`.
* `Lists' α true`: Proper ZFA prelists. Defined inductively from the empty ZFA prelist
  (`Lists'.nil`) and from appending a ZFA prelist to a proper ZFA prelist (`Lists'.cons a l`).
* `Lists α`: ZFA lists. Sum of the atoms and proper ZFA prelists.
* `Finsets α`: ZFA sets. Defined as `Lists` quotiented by `Lists.Equiv`, the extensional
  equivalence.
-/

variable {α : Type*}

inductive Lists'.{u} (α : Type u) : Bool → Type u
  | atom : α → Lists' α false
  | nil : Lists' α true
  | cons' {b} : Lists' α b → Lists' α true → Lists' α true
  deriving DecidableEq

compile_inductive% Lists'

def Lists (α : Type*) :=
  Σ b, Lists' α b

namespace Lists'

-- INSTANCE (free from Core): [Inhabited

def cons : Lists α → Lists' α true → Lists' α true
  | ⟨_, a⟩, l => cons' a l
