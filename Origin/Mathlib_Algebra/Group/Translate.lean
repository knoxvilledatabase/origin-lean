/-
Extracted from Algebra/Group/Translate.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Translation operator

This file defines the translation of a function from a group by an element of that group.

## Notation

`τ a f` is notation for `translate a f`.

## See also

Generally, translation is the same as acting on the domain by subtraction. This setting is
abstracted by `DomAddAct` in such a way that `τ a f = DomAddAct.mk (-a) +ᵥ f` (see
`translate_eq_domAddActMk_vadd`). Using `DomAddAct` is irritating in applications because of this
negation appearing inside `DomAddAct.mk`. Although mathematically equivalent, the pen and paper
convention is that translating is an action by subtraction, not by addition.
-/

open Function Set

open scoped Pointwise

variable {ι α β M G H : Type*} [AddCommGroup G]

def translate (a : G) (f : G → α) : G → α := fun x ↦ f (x - a)
