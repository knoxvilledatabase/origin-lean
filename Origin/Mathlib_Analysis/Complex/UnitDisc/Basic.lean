/-
Extracted from Analysis/Complex/UnitDisc/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Poincaré disc

In this file we define `Complex.UnitDisc` to be the unit disc in the complex plane. We also
introduce some basic operations on this disc.
-/

open Set Function Metric Filter

open scoped ComplexConjugate Topology

noncomputable section

namespace Complex

def UnitDisc : Type :=
  ball (0 : ℂ) 1 deriving TopologicalSpace
