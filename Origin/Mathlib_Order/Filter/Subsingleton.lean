/-
Extracted from Order/Filter/Subsingleton.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Subsingleton filters

We say that a filter `l` is a *subsingleton* if there exists a subsingleton set `s ∈ l`.
Equivalently, `l` is either `⊥` or `pure a` for some `a`.
-/

open Set

variable {α β : Type*} {l : Filter α}

namespace Filter

protected def Subsingleton (l : Filter α) : Prop := ∃ s ∈ l, Set.Subsingleton s

theorem Subsingleton.anti {l'} (hl : l.Subsingleton) (hl' : l' ≤ l) : l'.Subsingleton :=
  let ⟨s, hsl, hs⟩ := hl; ⟨s, hl' hsl, hs⟩
