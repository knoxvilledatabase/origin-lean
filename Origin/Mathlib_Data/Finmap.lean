/-
Extracted from Data/Finmap.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite maps over `Multiset`
-/

universe u v w

open List

variable {α : Type u} {β : α → Type v}

/-! ### Multisets of sigma types -/

namespace Multiset

def keys (s : Multiset (Sigma β)) : Multiset α :=
  s.map Sigma.fst
