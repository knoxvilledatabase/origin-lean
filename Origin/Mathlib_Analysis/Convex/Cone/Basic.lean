/-
Extracted from Analysis/Convex/Cone/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Proper cones

We define a *proper cone* as a closed, pointed cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once we have the definitions of conic and
linear programs, the results from this file can be used to prove duality theorems.

One can turn `C : PointedCone R E` + `hC : IsClosed C` into `C : ProperCone R E` in a tactic block
by doing `lift C to ProperCone R E using hC`.

One can also turn `C : ConvexCone 𝕜 E` + `hC : Set.Nonempty C ∧ IsClosed C` into
`C : ProperCone 𝕜 E` in a tactic block by doing `lift C to ProperCone 𝕜 E using hC`,
assuming `𝕜` is a dense topological field.

## TODO

The next steps are:
- Add `ConvexConeClass` that extends `SetLike` and replace the below instance
- Define primal and dual cone programs and prove weak duality.
- Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
- Define linear programs and prove LP duality as a special case of cone duality.
- Find a better reference (textbook instead of lecture notes).

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

open ContinuousLinearMap Filter Function Set

variable {𝕜 R E F G : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]

variable [AddCommMonoid E] [TopologicalSpace E] [Module R E]

variable [AddCommMonoid F] [TopologicalSpace F] [Module R F]

variable [AddCommMonoid G] [TopologicalSpace G] [Module R G]

local notation "R≥0" => {r : R // 0 ≤ r}

variable (R E) in

abbrev ProperCone := ClosedSubmodule R≥0 E

namespace ProperCone

section Module

variable {C C₁ C₂ : ProperCone R E} {r : R} {x : E}
