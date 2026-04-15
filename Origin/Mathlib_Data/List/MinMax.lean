/-
Extracted from Data/List/MinMax.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Minimum and maximum of lists

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f [] = none`

`minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/

namespace List

variable {α β : Type*}

section ArgAux

variable (r : α → α → Prop) [DecidableRel r] {l : List α} {o : Option α} {a : α}

def argAux (a : Option α) (b : α) : Option α :=
  Option.casesOn a (some b) fun c => if r b c then some b else some c
