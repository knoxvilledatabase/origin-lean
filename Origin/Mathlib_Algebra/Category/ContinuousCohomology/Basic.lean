/-
Extracted from Algebra/Category/ContinuousCohomology/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Continuous cohomology

We define continuous cohomology as the homology of homogeneous cochains.

## Implementation details

We define homogeneous cochains as `g`-invariant continuous function in `C(G, C(G,...,C(G, M)))`
instead of the usual `C(Gⁿ, M)` to allow more general topological groups other than locally compact
ones. For this to work, we also work in `Action (TopModuleCat R) G`, where the `G` action on `M`
is only continuous on `M`, and not necessarily continuous in both variables, because the `G` action
on `C(G, M)` might not be continuous on both variables even if it is on `M`.

For the differential map, instead of a finite sum we use the inductive definition
`d₋₁ : M → C(G, M) := const : m ↦ g ↦ m` and
`dₙ₊₁ : C(G, _) → C(G, C(G, _)) := const - C(G, dₙ) : f ↦ g ↦ f - dₙ (f (g))`
See `ContinuousCohomology.MultiInd.d`.

## Main definition
- `ContinuousCohomology.homogeneousCochains`:
  The functor taking an `R`-linear `G`-representation to the complex of homogeneous cochains.
- `continuousCohomology`:
  The functor taking an `R`-linear `G`-representation to its `n`-th continuous cohomology.

## TODO
- Show that it coincides with `groupCohomology` for discrete groups.
- Give the usual description of cochains in terms of `n`-ary functions for locally compact groups.
- Show that short exact sequences induce long exact sequences in certain scenarios.
-/

open CategoryTheory Functor ContinuousMap

variable (R G : Type*) [CommRing R] [Group G] [TopologicalSpace R]

namespace ContinuousCohomology

variable [TopologicalSpace G] [IsTopologicalGroup G]

variable {R G} in

abbrev Iobj (rep : Action (TopModuleCat R) G) : Action (TopModuleCat R) G where
  V := .of R C(G, rep.V)
  ρ :=
  { toFun g := TopModuleCat.ofHom
      { toFun f := .comp (rep.ρ g).hom (f.comp (Homeomorph.mulLeft g⁻¹))
        map_add' _ _ := by ext; simp
        map_smul' _ _ := by ext; simp
        cont := (continuous_postcomp _).comp (continuous_precomp _) }
    map_one' := ConcreteCategory.ext (by ext; simp)
    map_mul' _ _ := ConcreteCategory.ext (by ext; simp [mul_assoc]) }
