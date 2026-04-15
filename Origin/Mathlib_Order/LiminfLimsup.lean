/-
Extracted from Order/LiminfLimsup.lean
Genuine: 6 of 12 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# liminfs and limsups of functions and filters

Defines the liminf/limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.

We define `limsSup f` (`limsInf f`) where `f` is a filter taking values in a conditionally complete
lattice. `limsSup f` is the smallest element `a` such that, eventually, `u ≤ a` (and vice versa for
`limsInf f`). To work with the Limsup along a function `u` use `limsSup (map u f)`.

Usually, one defines the Limsup as `inf (sup s)` where the Inf is taken over all sets in the filter.
For instance, in ℕ along a function `u`, this is `inf_n (sup_{k ≥ n} u k)` (and the latter quantity
decreases with `n`, so this is in fact a limit.). There is however a difficulty: it is well possible
that `u` is not bounded on the whole space, only eventually (think of `limsup (fun x ↦ 1/x)` on ℝ).
Then there is no guarantee that the quantity above really decreases (the value of the `sup`
beforehand is not really well defined, as one cannot use ∞), so that the Inf could be anything.
So one cannot use this `inf sup ...` definition in conditionally complete lattices, and one has
to use a less tractable definition.

In conditionally complete lattices, the definition is only useful for filters which are eventually
bounded above (otherwise, the Limsup would morally be +∞, which does not belong to the space) and
which are frequently bounded below (otherwise, the Limsup would morally be -∞, which is not in the
space either). We start with definitions of these concepts for arbitrary filters, before turning to
the definitions of Limsup and Liminf.

In complete lattices, however, it coincides with the `Inf Sup` definition.
-/

open Filter Set Function

variable {α β γ ι ι' : Type*}

namespace Filter

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s : Set α} {u : β → α}

def limsSup (f : Filter α) : α :=
  sInf { a | ∀ᶠ n in f, n ≤ a }

def limsInf (f : Filter α) : α :=
  sSup { a | ∀ᶠ n in f, a ≤ n }

def limsup (u : β → α) (f : Filter β) : α :=
  limsSup (map u f)

def liminf (u : β → α) (f : Filter β) : α :=
  limsInf (map u f)

def blimsup (u : β → α) (f : Filter β) (p : β → Prop) :=
  sInf { a | ∀ᶠ x in f, p x → u x ≤ a }

def bliminf (u : β → α) (f : Filter β) (p : β → Prop) :=
  sSup { a | ∀ᶠ x in f, p x → a ≤ u x }

variable {f : Filter β} {u : β → α} {p : β → Prop}

end
