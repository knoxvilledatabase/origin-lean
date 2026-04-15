/-
Extracted from Geometry/Diffeology/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Diffeological spaces

A diffeological space is a concrete sheaf on the site of cartesian spaces ℝⁿ and smooth maps
between them, or equivalently a type `X` with a well-behaved notion of smoothness for functions from
the spaces ℝⁿ to X - see https://ncatlab.org/nlab/show/diffeological+space. In this file we focus on
the latter viewpoint and define some of the basic notions of diffeology, like diffeological spaces
and smooth maps between them.

Concretely, this means that for our purposes a diffeological space is a type `X` together with a set
`plots n` of maps ℝⁿ → X for each n (called plots), such that the following three properties hold:
* Every constant map is a plot.
* For every plot p : ℝⁿ → X and smooth map f : ℝᵐ → ℝⁿ, p ∘ f is a plot.
* Every map p : ℝⁿ → X that is locally smooth is a plot, where by locally smooth we mean that ℝⁿ can
  be covered by open sets U such that p ∘ f is a plot for every smooth f : ℝᵐ → U.

Every normed space, smooth manifold etc. is then naturally a diffeological space by simply taking
the plots to be those maps ℝⁿ → X that are smooth in the traditional sense. A map `f : X → Y`
between diffeological spaces is furthermore called smooth if postcomposition with it sends plots of
`X` to plots of `Y`. This is equivalent to the usual definition of smoothness for maps between e.g.
manifolds, and equivalent to being a plot for maps p : ℝⁿ → X.

In addition to this notion of smoothness, every diffeological space `X` also comes equipped with a
natural diffeology, called the D-topology; it is the finest topology on `X` that makes all plots
continuous, and consists precisely of those sets whose preimages under plots are all open. This
recovers the standard topology of e.g. normed spaces and manifolds, and makes all smooth maps
continuous. We provide this as a definition but not as an instance, for reasons outlined in the
implementation details below.

## Main definitions / results

* `DiffeologicalSpace X`: the type of diffeologies on a type `X`.
* `IsPlot p`: predicate stating that a map p : ℝⁿ → X is a plot, i.e. belongs to the diffeology
  on `X`.
* `DSmooth f`: predicate stating that a map `f : X → Y` between diffeological spaces is smooth in
  the sense that it sends plots to plots. This is the correct notion of morphisms between
  diffeological spaces.
* `dTopology`: the D-topology on a diffeological space, consisting of all sets `U` whose preimage
  `p ⁻¹' u` is open for all plots `p`. This is a definition rather than an instance to avoid
  typeclass diamonds (see below), and meant for use with notation such as
  `Continuous[_, dTopology]`.
* `IsDTopologyCompatible X`: typeclass stating that `X` is equipped with a topology that is equal
  (but not necessarily defeq) to the D-topology.
* `NormedSpace.toDiffeology`: the standard diffeology on any finite-dimensional normed space `X`,
  consisting of all conventionally smooth maps ℝⁿ → X. This is again a definition rather than a
  instance for typeclass diamond reasons; however, we do put this as an instance on `ℝ` and
  `EuclideanSpace ℝ ι` for finite `ι`.
* `IsContDiffCompatible X`: typeclass stating that the diffeology on a normed space `X` is equal to
  the diffeology whose plots are precisely the smooth maps.
* `isPlot_iff_dSmooth`: a map ℝⁿ → X is a plot iff it is smooth.
* `dSmooth_iff_contDiff`: a map between finite-dimensional normed spaces is smooth in the sense of
  `DSmooth` iff it is smooth in the sense of `ContDiff ℝ ∞`.

## Implementation notes

### Choice of test spaces

Instead of defining diffeologies as collections of plots ℝⁿ → X whose domains are the spaces ℝⁿ, we
could have also defined them in terms of maps from some other collection of test spaces; for
example:
* all open balls in the spaces ℝⁿ
* all open subsets of the spaces ℝⁿ
* all finite-dimensional normed spaces, or open balls therein / open subsets thereof
* all finite-dimensional smooth manifolds.

All of these result in equivalent notions of diffeologies and smooth maps; the abstract way to see
this is that the corresponding sites are all dense subsites of the site of finite-dimensional smooth
manifolds, and hence give rise to equivalent sheaf topoi. Which of those sites / collections of test
spaces to use is hence mainly a matter of convenience; we have gone with the cartesian spaces ℝⁿ
mainly for two reasons:
* They are the simplest to work with for practical purposes: maps between subsets are more annoying
  to deal with formally than maps between types, and e.g. smooth manifolds are extremely annoying
  to quantify over, while the cartesian spaces ℝⁿ are indexed simply by the natural numbers ℕ.
* Working with e.g. all finite-dimensional normed spaces instead of this particular choice of
  representatives would lead to an unnecessary universe bump.

One downside of this choice compared to that of all open subsets of ℝⁿ is however that it makes the
sheaf condition / locality condition of diffeologies ("any map that is locally a plot is also
globally a plot") somewhat awkward to state and prove. To mitigate this, we provide
`DiffeologicalSpace.ofPlotsOn` as a way to construct a diffeology from plots whose domains are
subsets of ℝⁿ. See the definition of `NormedSpace.toDiffeology` for an example where this is used.

### D-Topology

While the D-topology is quite well-behaved in some regards, it does unfortunately not always commute
with e.g. products. This means that it can not be registered as an instance - otherwise, there would
be two `TopologicalSpace`-instances on binary products, the product topology of the D-topologies on
the factors and the D-topology of the product diffeology. For emphasis we repeat: in general these
topologies can be mathematically distinct not just non-defeq. We thus instead define a typeclass
`IsDTopologyCompatible X` to express when the topology on `X` does match the D-topology, and also
give the D-topology the short name `dTopology` to enable use of notations such as
`Continuous[_, dTopology]` for continuity with respect to the D-topology.

In order to make it easier to work with diffeological spaces whose natural diffeology does match
the D-topology, we also include the D-topology as part of the data of `DiffeologicalSpace X`.
This allows the diffeologies on e.g. ℝⁿ, manifolds and quotients of diffeological spaces to be
defined in such a way that the D-topology is defeq to the topology that the space already carries.

### Diffeologies on normed spaces

Every normed spaces carries a natural diffeology consisting of all smooth maps from ℝⁿ. While this
"normed space diffeology" does commute with arbitrary products, we can't register it as an instance
because it wouldn't be defeq to the product diffeology on products of normed spaces. We thus only
give it as a definition (`NormedSpace.toDiffeology`) instead of an instance, and instead provide a
typeclass `IsContDiffCompatible X` for talking about normed spaces equipped with the normed space
diffeology.

To make working with finite-dimensional spaces easier, `NormedSpace.toDiffeology` is defined in such
a way that its D-topology is defeq to the topology induced by the norm - however, this currently
comes at the cost of making the definition work only on finite-dimensional spaces. It should be
possible to extend this to all normed spaces though in the future.

## TODO

Much of the basic theory of diffeological spaces has already been formalised at
https://github.com/peabrainiac/lean-orbifolds and just needs to be upstreamed. However, some TODOs
that haven't been formalised at all yet and only depend on the material here are:
* Generalise `NormedSpace.toDiffeology` to infinite-dimensional normed spaces. The hard part of this
  is showing that the D-topology of any normed space is just its usual topology, as is needed to
  make that equality definitional. On paper, this is relatively straightforward:
  for a set U ⊆ X that is not open under the standard normed space topology, take a sequence x_i
  outside of U that converges to a point in U, a smooth map ℝ → X under which a convergent sequence
  in ℝ maps to this sequence (x_i), and use it to conclude that U is not D-open either. However,
  constructing the needed smooth map explicitly is probably a lot of work.
* Generalise `dSmooth_iff_contDiff` to infinite-dimensional normed spaces if possible. There should
  be some references at least for the case of Banach spaces in the literature.

## References

* [Patrick Iglesias-Zemmour, *Diffeology*][zemmour2013diffeology]
* <https://ncatlab.org/nlab/show/diffeological+space>

## Tags
diffeology, diffeological space, smoothness, smooth function
-/

noncomputable section

assert_not_exists ChartedSpace

local macro:max "𝔼" noWs n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

open Topology ContDiff

class DiffeologicalSpace (X : Type*) where
  /-- The plots `EuclideanSpace ℝ (Fin n) → X` representing the smooth ways to map
  `EuclideanSpace ℝ (Fin n)` into `X`. This is the main
  piece of data underlying the diffeology. -/
  plots (n : ℕ) : Set (𝔼ⁿ → X)
  /-- Every constant map needs to be a plot. -/
  constant_plots {n : ℕ} (x : X) : (fun _ ↦ x) ∈ plots n
  /-- Smooth reparametrisations of plots need to be plots. -/
  plot_reparam {n m : ℕ} {p : 𝔼ᵐ → X} {f : 𝔼ⁿ → 𝔼ᵐ} (hp : p ∈ plots m) (hf : ContDiff ℝ ∞ f) :
    p ∘ f ∈ plots n
  /-- Every locally smooth map `EuclideanSpace ℝ (Fin n) → X` is a plot. -/
  locality {n : ℕ} {p : 𝔼ⁿ → X} (hp : ∀ x : 𝔼ⁿ, ∃ u : Set 𝔼ⁿ, IsOpen u ∧ x ∈ u ∧
    ∀ {m : ℕ} {f : 𝔼ᵐ → 𝔼ⁿ}, (∀ x, f x ∈ u) → ContDiff ℝ ∞ f → p ∘ f ∈ plots m) : p ∈ plots n
  /-- The D-topology of the diffeology. This is included as part of the data in order to give
  control over what the D-topology is defeq to. See also note [forgetful inheritance]. -/
  dTopology : TopologicalSpace X := {
    IsOpen u := ∀ ⦃n : ℕ⦄, ∀ p ∈ plots n, IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ _ ↦ isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp ↦
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp ↦
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu ↦ hs u hu p hp }
  /-- The D-topology consists of exactly those sets whose preimages under plots are all open. -/
  isOpen_iff_preimages_plots {u : Set X} :
    dTopology.IsOpen u ↔ ∀ {n : ℕ}, ∀ p ∈ plots n, IsOpen (p ⁻¹' u) := by rfl

namespace Diffeology

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

section Defs

alias dTopology := DiffeologicalSpace.dTopology
