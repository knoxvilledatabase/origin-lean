/-
Extracted from Geometry/Manifold/Algebra/Monoid.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `C^n` monoid
A `C^n` monoid is a monoid that is also a `C^n` manifold, in which multiplication is a `C^n` map
of the product manifold `G` × `G` into `G`.

In this file we define the basic structures to talk about `C^n` monoids: `ContMDiffMul` and its
additive counterpart `ContMDiffAdd`. These structures are general enough to also talk about `C^n`
semigroups.
-/

open scoped Manifold ContDiff

library_note «Design choices about smooth algebraic structures» /--

1. All `C^n` algebraic structures on `G` are `Prop`-valued classes that extend

   `IsManifold I n G`. This way we save users from adding both

   `[IsManifold I n G]` and `[ContMDiffMul I n G]` to the assumptions. While many API

   lemmas hold true without the `IsManifold I n G` assumption, we're not aware of a

   mathematically interesting monoid on a topological manifold such that (a) the space is not a

   `IsManifold`; (b) the multiplication is `C^n` at `(a, b)` in the charts

   `extChartAt I a`, `extChartAt I b`, `extChartAt I (a * b)`.

2. Because of `ModelProd` we can't assume, e.g., that a `LieGroup` is modelled on `𝓘(𝕜, E)`. So,

   we formulate the definitions and lemmas for any model.

3. While smoothness of an operation implies its continuity, lemmas like

   `continuousMul_of_contMDiffMul` can't be instances because otherwise Lean would have to search

   for `ContMDiffMul I n G` with unknown `𝕜`, `E`, `H`, and `I : ModelWithCorners 𝕜 E H`. If users

   need `[ContinuousMul G]` in a proof about a `C^n` monoid, then they need to either add

   `[ContinuousMul G]` as an assumption (worse) or use `haveI` in the proof (better).

-/

class ContMDiffAdd {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    (G : Type*) [Add G] [TopologicalSpace G] [ChartedSpace H G] : Prop
    extends IsManifold I n G where
  contMDiff_add : CMDiff n fun p : G × G ↦ p.1 + p.2
