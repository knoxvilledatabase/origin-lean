/-
Extracted from Geometry/Manifold/Bordism.lean
Genuine: 2 of 7 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
## (Unoriented) bordism theory

This file defines the beginnings of unoriented bordism theory. We define singular manifolds,
the building blocks of unoriented bordism groups. Future pull requests will define bordisms
and the bordism groups of a topological space, and prove these are abelian groups.

The basic notion of bordism theory is that of a bordism between smooth manifolds.
Two compact smooth `n`-dimensional manifolds `M` and `N` are **bordant** if there exists a smooth
**bordism** between them: this is a compact `n+1`-dimensional manifold `W` whose boundary is
(diffeomorphic to) the disjoint union `M ⊕ N`. Being bordant is an equivalence relation
(transitivity follows from the collar neighbourhood theorem). The set of equivalence classes has an
abelian group structure, with the group operation given as disjoint union of manifolds,
and is called the `n`-th (unoriented) bordism group.

This construction can be generalised one step further, to produce an extraordinary homology theory.
Given a topological space `X`, a **singular manifold** on `X` is a closed smooth manifold `M`
together with a continuous map `M → X`. (The word *singular* does not refer to singularities,
but is by analogy to singular chains in the definition of singular homology.)

Given two `n`-dimensional singular manifolds `s` and `t`, an (oriented) bordism between `s` and `t`
is a compact smooth `n+1`-dimensional manifold `W` whose boundary is (diffeomorphic to) the disjoint
union of `s` and `t`, together with a map `W → X` which restricts to the maps on `s` and `t`.
We call `s` and `t` bordant if there exists a bordism between them: again, this defines an
equivalence relation. The `n`-th bordism group of `X` is the set of bordism classes of
`n`-dimensional singular manifolds on `X`. If `X` is a single point, this recovers the bordism
groups from the preceding paragraph.

These absolute bordism groups can be generalised further to relative bordism groups, for each
topological pair `(X, A)`; in fact, these define an extra-ordinary homology theory.

## Main definitions

- **SingularManifold X k I**: a singular manifold on a topological space `X`, is a pair `(M, f)` of
  a closed `C^k`-manifold `M` modelled on `I` together with a continuous map `M → X`.
  We don't assume `M` to be modelled on `ℝⁿ`, but add the model topological space `H`,
  the vector space `E` and the model with corners `I` as type parameters.
  If we wish to emphasize the model, we will speak of a singular `I`-manifold.
  To define a disjoint union of singular manifolds, we require their domains to be manifolds
  over the same model with corners: this is why we make the model explicit.

## Main results

- `SingularManifold.map`: a map `X → Y` of topological spaces induces a map between the spaces
  of singular manifolds. This will be used to define functoriality of bordism groups.
- `SingularManifold.comap`: if `(N, f)` is a singular manifold on `X`
  and `φ : M → N` is continuous, the `comap` of `(N, f)` and `φ`
  is the induced singular manifold `(M, f ∘ φ)` on `X`.
- `SingularManifold.empty`: the empty set `M`, viewed as a manifold,
  as a singular manifold over any space `X`.
- `SingularManifold.toPUnit`: a smooth manifold induces a singular manifold on the one-point space.
- `SingularManifold.prod`: the product of a singular `I`-manifold and a singular `J`-manifold
  on the one-point space, is a singular `I.prod J`-manifold on the one-point space.
- `SingularManifold.sum`: the disjoint union of two singular `I`-manifolds
  is a singular `I`-manifold.

## Implementation notes

* We choose a bundled design for singular manifolds (and also for bordisms): to construct the
  group structure on the set of bordism classes, having that be a type is useful.
* The underlying model with corners is a type parameter, as defining a disjoint union of singular
  manifolds requires their domains to be manifolds over the same model with corners.
  Thus, either we restrict to manifolds modelled over `𝓡n` (which we prefer not to),
  or the model must be a type parameter.
* Having `SingularManifold` contain the type `M` as explicit structure field is not ideal,
  as this adds a universe parameter to the structure. However, this is the best solution we found:
  we generally cannot have `M` live in the same universe as `X` (a common case is `X` being
  `PUnit`), and determining the universe of `M` from the universes of `E` and `H` would make
  `SingularManifold.map` painful to state (as that would require `ULift`ing `M`).

## TODO
- define bordisms and prove basic constructions (e.g. reflexivity, symmetry, transitivity)
  and operations (e.g. disjoint union, sum with the empty set)
- define the bordism relation and prove it is an equivalence relation
- define the unoriented bordism group (the set of bordism classes) and prove it is an abelian group
- for bordisms on a one-point space, define multiplication and prove the bordism ring structure
- define relative bordism groups (generalising the previous three points)
- prove that relative unoriented bordism groups define an extraordinary homology theory

## Tags

singular manifold, bordism, bordism group
-/

open scoped Manifold

open Module Set

suppress_compilation

structure SingularManifold.{u} (X : Type*) [TopologicalSpace X] (k : WithTop ℕ∞)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) where
  /-- The manifold `M` of a singular `n`-manifold `(M, f)` -/
  M : Type u
  /-- The manifold `M` is a topological space. -/
  [topSpaceM : TopologicalSpace M]
  /-- The manifold `M` is a charted space over `H`. -/
  [chartedSpace : ChartedSpace H M]
  /-- `M` is a `C^k` manifold. -/
  [isManifold : IsManifold I k M]
  [compactSpace : CompactSpace M]
  [boundaryless : BoundarylessManifold I M]
  /-- The underlying map `M → X` of a singular `n`-manifold `(M, f)` on `X` -/
  f : M → X
  hf : Continuous f

namespace SingularManifold

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {k : WithTop ℕ∞}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I k M] [CompactSpace M] [BoundarylessManifold I M]

-- INSTANCE (free from Core): {s

-- INSTANCE (free from Core): {s

-- INSTANCE (free from Core): {s

-- INSTANCE (free from Core): {s

-- INSTANCE (free from Core): {s

def map.{u} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} (s : SingularManifold.{u} X k I)
    {φ : X → Y} (hφ : Continuous φ) : SingularManifold.{u} Y k I where
  M := s.M
  f := φ ∘ s.f
  hf := hφ.comp s.hf
