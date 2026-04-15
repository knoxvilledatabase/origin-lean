/-
Extracted from Order/Filter/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Theory of filters on sets

A *filter* on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

## Main definitions

In this file, we endow `Filter α` it with a complete lattice structure.
This structure is lifted from the lattice structure on `Set (Set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `Filter` is a monadic functor, with a push-forward operation
`Filter.map` and a pull-back operation `Filter.comap` that form a Galois connections for the
order on filters.

The examples of filters appearing in the description of the two motivating ideas are:
* `(Filter.atTop : Filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in `Mathlib/Topology/UniformSpace/Basic.lean`)
* `MeasureTheory.ae` : made of sets whose complement has zero measure with respect to `μ`
  (defined in `Mathlib/MeasureTheory/OuterMeasure/AE`)

The predicate "happening eventually" is `Filter.Eventually`, and "happening often" is
`Filter.Frequently`, whose definitions are immediate after `Filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).
## Notation

* `∀ᶠ x in f, p x` : `f.Eventually p`;
* `∃ᶠ x in f, p x` : `f.Frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `𝓟 s` : `Filter.Principal s`, localized in `Filter`.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`, which
we do *not* require. This gives `Filter X` better formal properties, in particular a bottom element
`⊥` for its lattice structure, at the cost of including the assumption
`[NeBot f]` in a number of lemmas and definitions.
-/

assert_not_exists IsOrderedRing Fintype

open Function Set Order

open scoped symmDiff

universe u v w x y

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

-- INSTANCE (free from Core): inhabitedMem

theorem filter_eq_iff : f = g ↔ f.sets = g.sets :=
  ⟨congr_arg _, filter_eq⟩
