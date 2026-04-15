/-
Extracted from Topology/Category/CompHausLike/Basic.lean
Genuine: 3 of 9 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!

# Categories of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces satisfying an additional property `P`.

## Implementation

We define a structure `CompHausLike` which takes as an argument a predicate `P` on topological
spaces. It consists of the data of a topological space, satisfying the additional properties of
being compact and Hausdorff, and satisfying `P`. We give a category structure to `CompHausLike P`
induced by the forgetful functor to topological spaces.

It used to be the case (before https://github.com/leanprover-community/mathlib4/pull/12930 was merged) that several different categories of compact
Hausdorff spaces, possibly satisfying some extra property, were defined from scratch in this way.
For example, one would define a structure `CompHaus` as follows:

```lean
structure CompHaus where
  toTop : TopCat
  [is_compact : CompactSpace toTop]
  [is_hausdorff : T2Space toTop]
```

and give it the category structure induced from topological spaces. Then the category of profinite
spaces was defined as follows:

```lean
structure Profinite where
  toCompHaus : CompHaus
  [isTotallyDisconnected : TotallyDisconnectedSpace toCompHaus]
```

The categories `Stonean` consisting of extremally disconnected compact Hausdorff spaces and
`LightProfinite` consisting of totally disconnected, second countable compact Hausdorff spaces were
defined in a similar way. This resulted in code duplication, and reducing this duplication was part
of the motivation for introducing `CompHausLike`.

Using `CompHausLike`, we can now define
`CompHaus := CompHausLike (fun _ ↦ True)`
`Profinite := CompHausLike (fun X ↦ TotallyDisconnectedSpace X)`.
`Stonean := CompHausLike (fun X ↦ ExtremallyDisconnected X)`.
`LightProfinite := CompHausLike  (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X)`.

These four categories are important building blocks of condensed objects (see the files
`Condensed.Basic` and `Condensed.Light.Basic`). These categories share many properties and often,
one wants to argue about several of them simultaneously. This is the other part of the motivation
for introducing `CompHausLike`. On paper, one would say "let `C` be on of the categories `CompHaus`
or `Profinite`, then the following holds: ...". This was not possible in Lean using the old
definitions. Using the new definitions, this becomes a matter of identifying what common property
of `CompHaus` and `Profinite` is used in the proof in question, and then proving the theorem for
`CompHausLike P` satisfying that property, and it will automatically apply to both `CompHaus` and
`Profinite`.
-/

universe u

open CategoryTheory

variable (P : TopCat.{u} → Prop)

structure CompHausLike where
  /-- The underlying topological space of an object of `CompHausLike P`. -/
  toTop : TopCat
  /-- The underlying topological space is compact. -/
  [is_compact : CompactSpace toTop]
  /-- The underlying topological space is T2. -/
  [is_hausdorff : T2Space toTop]
  /-- The underlying topological space satisfies P. -/
  prop : P toTop

namespace CompHausLike

attribute [instance] is_compact is_hausdorff

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): category

-- INSTANCE (free from Core): concreteCategory

-- INSTANCE (free from Core): hasForget₂

variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]

class HasProp : Prop where
  hasProp : P (TopCat.of X)

-- INSTANCE (free from Core): (X

variable [HasProp P X]

abbrev of : CompHausLike P where
  toTop := TopCat.of X
  is_compact := ‹_›
  is_hausdorff := ‹_›
  prop := HasProp.hasProp
