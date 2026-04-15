/-
Extracted from Topology/Algebra/ProperConstSMul.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Actions by proper maps

In this file we define `ProperConstSMul M X` to be a mixin `Prop`-value class
stating that `(c • ·)` is a proper map for all `c`.

Note that this is **not** the same as a proper action (not yet in `Mathlib`)
which requires `(c, x) ↦ (c • x, x)` to be a proper map.

We also provide 4 instances:
- for a continuous action on a compact Hausdorff space,
- and for a continuous group action on a general space;
- for the action on `X × Y`;
- for the action on `∀ i, X i`.
-/

class ProperConstVAdd (M X : Type*) [VAdd M X] [TopologicalSpace X] : Prop where
  /-- `(c +ᵥ ·)` is a proper map. -/
  isProperMap_vadd (c : M) : IsProperMap ((c +ᵥ ·) : X → X)
