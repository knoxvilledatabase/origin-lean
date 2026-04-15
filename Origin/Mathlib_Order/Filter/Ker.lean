/-
Extracted from Order/Filter/Ker.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Kernel of a filter

In this file we define the *kernel* `Filter.ker f` of a filter `f`
to be the intersection of all its sets.

We also prove that `Filter.principal` and `Filter.ker` form a Galois coinsertion
and prove other basic theorems about `Filter.ker`.
-/

open Function Set

namespace Filter

variable {ι : Sort*} {α β : Type*} {f g : Filter α} {s : Set α} {a : α}

lemma ker_def (f : Filter α) : f.ker = ⋂ s ∈ f, s := sInter_eq_biInter
