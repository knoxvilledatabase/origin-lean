/-
Extracted from Geometry/Manifold/Diffeomorph.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Diffeomorphisms
This file implements diffeomorphisms.

## Definitions

* `Diffeomorph I I' M M' n`: `n`-times continuously differentiable diffeomorphism between
  `M` and `M'` with respect to I and I'; we do not introduce a separate definition for the case
  `n = ∞` or `n = ω`; we use notation instead.
* `Diffeomorph.toHomeomorph`: reinterpret a diffeomorphism as a homeomorphism.
* `ContinuousLinearEquiv.toDiffeomorph`: reinterpret a continuous equivalence as
  a diffeomorphism.
* `ModelWithCorners.transContinuousLinearEquiv`: compose a given `ModelWithCorners` with a
  continuous linear equiv between the old and the new target spaces. Useful, e.g, to turn any
  finite-dimensional manifold into a manifold modelled on a Euclidean space.
* `Diffeomorph.toTransContinuousLinearEquiv`: the identity diffeomorphism between `M` with
  model `I` and `M` with model `I.transContinuousLinearEquiv e`.

This file also provides diffeomorphisms related to products and disjoint unions.
* `Diffeomorph.prodCongr`: the product of two diffeomorphisms
* `Diffeomorph.prodComm`: `M × N` is diffeomorphic to `N × M`
* `Diffeomorph.prodAssoc`: `(M × N) × N'` is diffeomorphic to `M × (N × N')`
* `Diffeomorph.sumCongr`: the disjoint union of two diffeomorphisms
* `Diffeomorph.sumComm`: `M ⊕ M'` is diffeomorphic to `M' × M`
* `Diffeomorph.sumAssoc`: `(M ⊕ N) ⊕ P` is diffeomorphic to `M ⊕ (N ⊕ P)`
* `Diffeomorph.sumEmpty`: `M ⊕ ∅` is diffeomorphic to `M`

## Notation

* `M ≃ₘ^n⟮I, I'⟯ M'`  := `Diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'`    := `Diffeomorph I J M N ∞`
* `E ≃ₘ^n[𝕜] E'`     := `E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`
* `E ≃ₘ[𝕜] E'`       := `E ≃ₘ⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Keywords

diffeomorphism, manifold
-/

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*} [TopologicalSpace H] {H' : Type*}
  [TopologicalSpace H'] {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}
  {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M'] {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {N' : Type*}
  [TopologicalSpace N'] [ChartedSpace G' N'] {n : WithTop ℕ∞}

section Defs

variable (I I' M M' n)

structure Diffeomorph extends M ≃ M' where
  protected contMDiff_toFun : CMDiff n toEquiv
  protected contMDiff_invFun : CMDiff n toEquiv.symm

end Defs
