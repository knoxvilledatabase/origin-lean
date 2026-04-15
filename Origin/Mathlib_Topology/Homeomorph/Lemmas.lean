/-
Extracted from Topology/Homeomorph/Lemmas.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Further properties of homeomorphisms

This file proves further properties of homeomorphisms between topological spaces.
Pretty much every topological property is preserved under homeomorphisms.

-/

assert_not_exists Module MonoidWithZero

open Filter Function Set Topology

variable {X Y W Z : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

namespace Homeomorph

protected theorem baireSpace [BaireSpace X] (f : X ≃ₜ Y) : BaireSpace Y :=
  f.isOpenQuotientMap.baireSpace
