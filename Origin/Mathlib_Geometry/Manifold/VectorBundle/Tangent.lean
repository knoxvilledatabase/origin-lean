/-
Extracted from Geometry/Manifold/VectorBundle/Tangent.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Tangent bundles

This file defines the tangent bundle as a `C^n` vector bundle.

Let `M` be a manifold with model `I` on `(E, H)`. The tangent space `TangentSpace I (x : M)` has
already been defined as a type synonym for `E`, and the tangent bundle `TangentBundle I M` as an
abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`.

In this file, when `M` is `C^1`, we construct a vector bundle structure
on `TangentBundle I M` using the `VectorBundleCore` construction indexed by the charts of `M`
with fibers `E`. Given two charts `i, j : OpenPartialHomeomorph M H`, the coordinate change
between `i` and `j` at a point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`.
This defines a vector bundle `TangentBundle` with fibers `TangentSpace`.

## Main definitions and results

* `tangentBundleCore I M` is the vector bundle core for the tangent bundle over `M`.

* When `M` is a `C^{n+1}` manifold, `TangentBundle I M` has a `C^n` vector bundle
  structure over `M`. In particular, it is a topological space, a vector bundle, a fiber bundle,
  and a `C^n` manifold.
-/

open Bundle Set IsManifold OpenPartialHomeomorph ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff

noncomputable section

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem contDiffOn_fderiv_coord_change [IsManifold I (n + 1) M]
    (i j : atlas H M) :
    ContDiffOn 𝕜 n (fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I))
      ((i.1.extend I).symm ≫ j.1.extend I).source := by
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source ⊆ range I := by
    refine I.extendCoordChange_source.trans_subset ?_; apply image_subset_range
  intro x hx
  refine (ContDiffWithinAt.fderivWithin_right ?_ I.uniqueDiffOn le_rfl
    <| h hx).mono h
  refine (I.contDiffOn_extendCoordChange (subset_maximalAtlas i.2)
    (subset_maximalAtlas j.2) x hx).mono_of_mem_nhdsWithin ?_
  exact I.extendCoordChange_source_mem_nhdsWithin hx

open IsManifold

variable [IsManifold I 1 M] [IsManifold I' 1 M']

variable (I M) in
