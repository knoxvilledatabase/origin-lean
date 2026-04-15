/-
Extracted from Topology/Category/LightProfinite/Basic.lean
Genuine: 6 of 10 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!

# Light profinite spaces

We construct the category `LightProfinite` of light profinite topological spaces. These are
implemented as totally disconnected second countable compact Hausdorff spaces.

This file also defines the category `LightDiagram`, which consists of those spaces that can be
written as a sequential limit (in `Profinite`) of finite sets.

We define an equivalence of categories `LightProfinite ≌ LightDiagram` and prove that these are
essentially small categories.

## Implementation

The category `LightProfinite` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/

universe v u

open CategoryTheory Limits Opposite FintypeCat Topology TopologicalSpace CompHausLike

abbrev LightProfinite := CompHausLike
  (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X)

namespace LightProfinite

-- INSTANCE (free from Core): (X

abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X] : LightProfinite :=
  CompHausLike.of _ X

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): {X

end LightProfinite

abbrev lightToProfinite : LightProfinite ⥤ Profinite :=
  CompHausLike.toCompHausLike (fun _ ↦ inferInstance)

abbrev lightToProfiniteFullyFaithful : lightToProfinite.FullyFaithful :=
  fullyFaithfulToCompHausLike _

abbrev lightProfiniteToCompHaus : LightProfinite ⥤ CompHaus :=
  compHausLikeToCompHaus _

abbrev LightProfinite.toTopCat : LightProfinite ⥤ TopCat :=
  CompHausLike.compHausLikeToTop _

section DiscreteTopology

attribute [local instance] FintypeCat.botTopology

attribute [local instance] FintypeCat.discreteTopology
