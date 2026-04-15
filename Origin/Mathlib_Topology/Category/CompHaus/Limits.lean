/-
Extracted from Topology/Category/CompHaus/Limits.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Category.CompHausLike.Limits

/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib.Topology.Category.CompHausLike.Limits`) to the special case of `CompHaus`.
-/

namespace CompHaus

universe u w

open CategoryTheory Limits CompHausLike

instance : HasExplicitPullbacks (fun _ ↦ True) where
  hasProp _ _ := inferInstance

instance : HasExplicitFiniteCoproducts.{w, u} (fun _ ↦ True) where
  hasProp _ := inferInstance

example : FinitaryExtensive CompHaus.{u} := inferInstance

abbrev isTerminalPUnit : IsTerminal (CompHaus.of PUnit.{u + 1}) := CompHausLike.isTerminalPUnit

noncomputable def terminalIsoPUnit : ⊤_ CompHaus.{u} ≅ CompHaus.of PUnit :=
  terminalIsTerminal.uniqueUpToIso CompHaus.isTerminalPUnit

noncomputable example : PreservesFiniteCoproducts compHausToTop := inferInstance

end CompHaus
