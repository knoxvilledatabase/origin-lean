/-
Extracted from Topology/Category/Profinite/Limits.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of `Profinite`.
-/

namespace Profinite

universe u w

open CategoryTheory Limits CompHausLike

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

abbrev isTerminalPUnit : IsTerminal (Profinite.of PUnit.{u + 1}) := CompHausLike.isTerminalPUnit

example : FinitaryExtensive Profinite.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts profiniteToCompHaus := inferInstance

end Profinite
