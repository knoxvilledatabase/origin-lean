/-
Extracted from Topology/Category/LightProfinite/Limits.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of
`LightProfinite`.
-/

namespace LightProfinite

universe u w

open CategoryTheory Limits CompHausLike

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

abbrev isTerminalPUnit : IsTerminal (LightProfinite.of PUnit.{u + 1}) :=
  CompHausLike.isTerminalPUnit

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): {X

example : FinitaryExtensive LightProfinite.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts lightProfiniteToCompHaus.{u} := inferInstance

end LightProfinite
