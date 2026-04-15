/-
Extracted from GroupTheory/FreeGroup/Orbit.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
For any `w : α × Bool`, `FreeGroup.startsWith w` is the set of all elements of `FreeGroup α` that
start with `w`.

The main theorem `Orbit.duplicate` proves that applying `w⁻¹` to the orbit of `x` under the action
of `FreeGroup.startsWith w` yields the orbit of `x` under the action of `FreeGroup.startsWith v`
for every `v ≠ w⁻¹` (and the point `x`).
-/

variable {α X : Type*} [DecidableEq α]

namespace FreeGroup

def startsWith (w : α × Bool) := {g : FreeGroup α | (FreeGroup.toWord g)[0]? = some w}

-- DISSOLVED: startsWith.ne_one
