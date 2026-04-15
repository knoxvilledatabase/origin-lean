/-
Extracted from Topology/Category/LightProfinite/Limits.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.LightProfinite.Basic

/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib.Topology.Category.CompHausLike.Limits`) to the special case of `LightProfinite`.
-/

namespace LightProfinite

universe u w

open CategoryTheory Limits CompHausLike

instance : HasExplicitPullbacks
    (fun Y ↦ TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) where
  hasProp _ _ := {
    hasProp := ⟨show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance,
      show SecondCountableTopology {_xy : _ | _} from inferInstance⟩ }

instance : HasExplicitFiniteCoproducts.{w, u}
    (fun Y ↦ TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) where
  hasProp _ := { hasProp :=
    ⟨show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance,
      show SecondCountableTopology (Σ (_a : _), _) from inferInstance⟩ }

abbrev isTerminalPUnit : IsTerminal (LightProfinite.of PUnit.{u + 1}) :=
  CompHausLike.isTerminalPUnit

example : FinitaryExtensive LightProfinite.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts lightProfiniteToCompHaus.{u} := inferInstance

end LightProfinite
