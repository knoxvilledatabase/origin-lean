/-
Extracted from MeasureTheory/Group/FundamentalDomain.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fundamental domain of a group action

A set `s` is said to be a *fundamental domain* of an action of a group `G` on a measurable space `α`
with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure-preserving action, any two
fundamental domains have the same measure, and for a `G`-invariant function, its integrals over any
two fundamental domains are equal to each other.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.

* We define the `HasFundamentalDomain` typeclass, in particular to be able to define the `covolume`
  of a quotient of `α` by a group `G`, which under reasonable conditions does not depend on the
  choice of fundamental domain.

* We define the `QuotientMeasureEqMeasurePreimage` typeclass to describe a situation in which a
  measure `μ` on `α ⧸ G` can be computed by taking a measure `ν` on `α` of the intersection of the
  pullback with a fundamental domain.

## Main declarations

* `MeasureTheory.IsFundamentalDomain`: Predicate for a set to be a fundamental domain of the
  action of a group
* `MeasureTheory.fundamentalFrontier`: Fundamental frontier of a set under the action of a group.
  Elements of `s` that belong to some other translate of `s`.
* `MeasureTheory.fundamentalInterior`: Fundamental interior of a set under the action of a group.
  Elements of `s` that do not belong to any other translate of `s`.
-/

open scoped ENNReal Pointwise Topology NNReal ENNReal MeasureTheory

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Filter

namespace MeasureTheory

structure IsAddFundamentalDomain (G : Type*) {α : Type*} [Zero G] [VAdd G α] [MeasurableSpace α]
    (s : Set α) (μ : Measure α := by volume_tac) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ s
  protected aedisjoint : Pairwise <| (AEDisjoint μ on fun g : G => g +ᵥ s)
