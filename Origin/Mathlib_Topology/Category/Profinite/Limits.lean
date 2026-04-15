/-
Extracted from Topology/Category/Profinite/Limits.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.CompHausLike.Limits

/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib.Topology.Category.CompHausLike.Limits`) to the special case of `Profinite`.
-/

namespace Profinite

universe u w

open CategoryTheory Limits CompHausLike

instance : HasExplicitPullbacks (fun Y ↦ TotallyDisconnectedSpace Y) where
  hasProp _ _ := { hasProp :=
    show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance}

instance : HasExplicitFiniteCoproducts.{w, u} (fun Y ↦ TotallyDisconnectedSpace Y) where
  hasProp _ := { hasProp :=
    show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance}

abbrev isTerminalPUnit : IsTerminal (Profinite.of PUnit.{u + 1}) := CompHausLike.isTerminalPUnit

example : FinitaryExtensive Profinite.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts profiniteToCompHaus := inferInstance

end Profinite
