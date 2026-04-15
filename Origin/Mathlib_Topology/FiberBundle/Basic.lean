/-
Extracted from Topology/FiberBundle/Basic.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fiber bundles

Mathematically, a (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on
`B` for which the fibers are all homeomorphic to `F`, such that the local situation around each
point is a direct product.

In our formalism, a fiber bundle is by definition the type `Bundle.TotalSpace F E` where
`E : B → Type*` is a function associating to `x : B` the fiber over `x`. This type
`Bundle.TotalSpace F E` is a type of pairs `⟨proj : B, snd : E proj⟩`.

To have a fiber bundle structure on `Bundle.TotalSpace F E`, one should
additionally have the following data:

* `F` should be a topological space;
* There should be a topology on `Bundle.TotalSpace F E`, for which the projection to `B` is
  a fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological space, and the injection
  from `E x` to `Bundle.TotalSpace F E` should be an embedding;
* There should be a distinguished set of bundle trivializations, the "trivialization atlas"
* There should be a choice of bundle trivialization at each point, which belongs to this atlas.

If all these conditions are satisfied, we register the typeclass `FiberBundle F E`.

It is in general nontrivial to construct a fiber bundle. A way is to start from the knowledge of
how changes of local trivializations act on the fiber. From this, one can construct the total space
of the bundle and its topology by a suitable gluing construction. The main content of this file is
an implementation of this construction: starting from an object of type
`FiberBundleCore` registering the trivialization changes, one gets the corresponding
fiber bundle and projection.

Similarly we implement the object `FiberPrebundle` which allows to define a topological
fiber bundle from trivializations given as partial equivalences with minimum additional properties.

## Main definitions

### Basic definitions

* `FiberBundle F E` : Structure saying that `E : B → Type*` is a fiber bundle with fiber `F`.

### Construction of a bundle from trivializations

* `Bundle.TotalSpace F E` is the type of pairs `(proj : B, snd : E proj)`. We can use the extra
  argument `F` to construct topology on the total space.
* `FiberBundleCore ι B F` : structure registering how changes of coordinates act
  on the fiber `F` above open subsets of `B`, where local trivializations are indexed by `ι`.

Let `Z : FiberBundleCore ι B F`. Then we define

* `Z.Fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.TotalSpace`  : the total space of `Z`, defined as `Bundle.TotalSpace F Z.Fiber` with a custom
                    topology.
* `Z.proj`        : projection from `Z.TotalSpace` to `B`. It is continuous.
* `Z.localTriv i` : for `i : ι`, bundle trivialization above the set `Z.baseSet i`, which is an
                    open set in `B`.

* `FiberPrebundle F E` : structure registering a cover of prebundle trivializations
  and requiring that the relative transition maps are open partial homeomorphisms.
* `FiberPrebundle.totalSpaceTopology a` : natural topology of the total space, making
  the prebundle into a bundle.

## Implementation notes

### Data vs mixins

For both fiber and vector bundles, one faces a choice: should the definition state the *existence*
of local trivializations (a propositional typeclass), or specify a fixed atlas of trivializations (a
typeclass containing data)?

In their initial mathlib implementations, both fiber and vector bundles were defined
propositionally. For vector bundles, this turns out to be mathematically wrong: in infinite
dimension, the transition function between two trivializations is not automatically continuous as a
map from the base `B` to the endomorphisms `F →L[R] F` of the fiber (considered with the
operator-norm topology), and so the definition needs to be modified by restricting consideration to
a family of trivializations (constituting the data) which are all mutually-compatible in this sense.
The PRs https://github.com/leanprover-community/mathlib/pull/13052 and
https://github.com/leanprover-community/mathlib/pull/13175 implemented this change.

There is still the choice about whether to hold this data at the level of fiber bundles or of vector
bundles. As of PR https://github.com/leanprover-community/mathlib/pull/17505, the data is all held
in `FiberBundle`, with `VectorBundle` a (propositional) mixin stating fiberwise-linearity.

This allows bundles to carry instances of typeclasses in which the scalar field, `R`, does not
appear as a parameter. Notably, we would like a vector bundle over `R` with fiber `F` over base `B`
to be a `ChartedSpace (B × F)`, with the trivializations providing the charts. This would be a
dangerous instance for typeclass inference, because `R` does not appear as a parameter in
`ChartedSpace (B × F)`. But if the data of the trivializations is held in `FiberBundle`, then a
fiber bundle with fiber `F` over base `B` can be a `ChartedSpace (B × F)`, and this is safe for
typeclass inference.

We expect that this choice of definition will also streamline constructions of fiber bundles with
similar underlying structure (e.g., the same bundle being both a real and complex vector bundle).

### Core construction

A fiber bundle with fiber `F` over a base `B` is a family of spaces isomorphic to `F`,
indexed by `B`, which is locally trivial in the following sense: there is a covering of `B` by open
sets such that, on each such open set `s`, the bundle is isomorphic to `s × F`.

To construct a fiber bundle formally, the main data is what happens when one changes trivializations
from `s × F` to `s' × F` on `s ∩ s'`: one should get a family of homeomorphisms of `F`, depending
continuously on the base point, satisfying basic compatibility conditions (cocycle property).
Useful classes of bundles can then be specified by requiring that these homeomorphisms of `F`
belong to some subgroup, preserving some structure (the "structure group of the bundle"): then
these structures are inherited by the fibers of the bundle.

Given such trivialization change data (encoded below in a structure called
`FiberBundleCore`), one can construct the fiber bundle. The intrinsic canonical
mathematical construction is the following.
The fiber above `x` is the disjoint union of `F` over all trivializations, modulo the gluing
identifications: one gets a fiber which is isomorphic to `F`, but non-canonically
(each choice of one of the trivializations around `x` gives such an isomorphism). Given a
trivialization over a set `s`, one gets an isomorphism between `s × F` and `proj^{-1} s`, by using
the identification corresponding to this trivialization. One chooses the topology on the bundle that
makes all of these into homeomorphisms.

For the practical implementation, it turns out to be more convenient to avoid completely the
gluing and quotienting construction above, and to declare above each `x` that the fiber is `F`,
but thinking that it corresponds to the `F` coming from the choice of one trivialization around `x`.
This has several practical advantages:
* without any work, one gets a topological space structure on the fiber. And if `F` has more
  structure it is inherited for free by the fiber.
* In the case of the tangent bundle of manifolds, this implies that on vector spaces the derivative
  (from `F` to `F`) and the manifold derivative (from `TangentSpace I x` to `TangentSpace I' (f x)`)
  are equal.

A drawback is that some silly constructions will typecheck: in the case of the tangent bundle, one
can add two vectors in different tangent spaces (as they both are elements of `F` from the point of
view of Lean). To solve this, one could mark the tangent space as irreducible, but then one would
lose the identification of the tangent space to `F` with `F`. There is however a big advantage of
this situation: even if Lean cannot check that two basepoints are defeq, it will accept the fact
that the tangent spaces are the same. For instance, if two maps `f` and `g` are locally inverse to
each other, one can express that the composition of their derivatives is the identity of
`TangentSpace I x`. One could fear issues as this composition goes from `TangentSpace I x` to
`TangentSpace I (g (f x))` (which should be the same, but should not be obvious to Lean
as it does not know that `g (f x) = x`). As these types are the same to Lean (equal to `F`), there
are in fact no dependent type difficulties here!

For this construction of a fiber bundle from a `FiberBundleCore`, we should thus
choose for each `x` one specific trivialization around it. We include this choice in the definition
of the `FiberBundleCore`, as it makes some constructions more
functorial and it is a nice way to say that the trivializations cover the whole space `B`.

With this definition, the type of the fiber bundle space constructed from the core data is
`Bundle.TotalSpace F (fun b : B ↦ F)`, but the topology is not the product one, in general.

We also take the indexing type (indexing all the trivializations) as a parameter to the fiber bundle
core: it could always be taken as a subtype of all the maps from open subsets of `B` to continuous
maps of `F`, but in practice it will sometimes be something else. For instance, on a manifold, one
will use the set of charts as a good parameterization for the trivializations of the tangent bundle.
Or for the pullback of a `FiberBundleCore`, the indexing type will be the same as
for the initial bundle.

## Tags
Fiber bundle, topological bundle, structure group
-/

variable {ι B F X : Type*} [TopologicalSpace X]

open TopologicalSpace Filter Set Bundle Topology

/-! ### General definition of fiber bundles -/

section FiberBundle

variable (F)

variable [TopologicalSpace B] [TopologicalSpace F] (E : B → Type*)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]

class FiberBundle where
  totalSpaceMk_isInducing' : ∀ b : B, IsInducing (@TotalSpace.mk B F E b)
  trivializationAtlas' : Set (Trivialization F (π F E))
  trivializationAt' : B → Trivialization F (π F E)
  mem_baseSet_trivializationAt' : ∀ b : B, b ∈ (trivializationAt' b).baseSet
  trivialization_mem_atlas' : ∀ b : B, trivializationAt' b ∈ trivializationAtlas'

namespace FiberBundle

variable [FiberBundle F E] (b : B)

theorem totalSpaceMk_isInducing : IsInducing (@TotalSpace.mk B F E b) := totalSpaceMk_isInducing' b

abbrev trivializationAtlas : Set (Trivialization F (π F E)) := trivializationAtlas'

abbrev trivializationAt : Trivialization F (π F E) := trivializationAt' b

theorem mem_baseSet_trivializationAt : b ∈ (trivializationAt F E b).baseSet :=
  mem_baseSet_trivializationAt' b

theorem trivialization_mem_atlas : trivializationAt F E b ∈ trivializationAtlas F E :=
  trivialization_mem_atlas' b

end FiberBundle

export FiberBundle (totalSpaceMk_isInducing trivializationAtlas trivializationAt

  mem_baseSet_trivializationAt trivialization_mem_atlas)

variable {F}

variable {E}
