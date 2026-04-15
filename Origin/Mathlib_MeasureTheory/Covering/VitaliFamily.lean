/-
Extracted from MeasureTheory/Covering/VitaliFamily.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Vitali families

On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets with
nonempty interiors, called `setsAt x`. This family is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `setsAt x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.

This file gives the basic definition of Vitali families. More interesting developments of this
notion are deferred to other files:
* constructions of specific Vitali families are provided by the Besicovitch covering theorem, in
  `Besicovitch.vitaliFamily`, and by the Vitali covering theorem, in `Vitali.vitaliFamily`.
* The main theorem on differentiation of measures along a Vitali family is proved in
  `VitaliFamily.ae_tendsto_rnDeriv`.

## Main definitions

* `VitaliFamily μ` is a structure made, for each `x : X`, of a family of sets around `x`, such that
  one can extract an almost everywhere disjoint covering from any subfamily containing sets of
  arbitrarily small diameters.

Let `v` be such a Vitali family.
* `v.FineSubfamilyOn` describes the subfamilies of `v` from which one can extract almost
  everywhere disjoint coverings. This property, called
  `v.FineSubfamilyOn.exists_disjoint_covering_ae`, is essentially a restatement of the definition
  of a Vitali family. We also provide an API to use efficiently such a disjoint covering.
* `v.filterAt x` is a filter on sets of `X`, such that convergence with respect to this filter
  means convergence when sets in the Vitali family shrink towards `x`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.8][Federer1996]
  (Vitali families are called Vitali relations there)
-/

open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure

open scoped Topology

variable {X : Type*} [PseudoMetricSpace X]

structure VitaliFamily {m : MeasurableSpace X} (μ : Measure X) where
  /-- Sets of the family "centered" at a given point. -/
  setsAt : X → Set (Set X)
  /-- All sets of the family are measurable. -/
  measurableSet : ∀ x : X, ∀ s ∈ setsAt x, MeasurableSet s
  /-- All sets of the family have nonempty interior. -/
  nonempty_interior : ∀ x : X, ∀ s ∈ setsAt x, (interior s).Nonempty
  /-- For any closed ball around `x`, there exists a set of the family contained in this ball. -/
  nontrivial : ∀ (x : X), ∀ ε > (0 : ℝ), ∃ s ∈ setsAt x, s ⊆ closedBall x ε
  /-- Consider a (possibly non-measurable) set `s`,
  and for any `x` in `s` a subfamily `f x` of `setsAt x`
  containing sets of arbitrarily small diameter.
  Then one can extract a disjoint subfamily covering almost all `s`. -/
  covering : ∀ (s : Set X) (f : X → Set (Set X)),
    (∀ x ∈ s, f x ⊆ setsAt x) → (∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ t ∈ f x, t ⊆ closedBall x ε) →
    ∃ t : Set (X × Set X), (∀ p ∈ t, p.1 ∈ s) ∧ (t.PairwiseDisjoint fun p ↦ p.2) ∧
      (∀ p ∈ t, p.2 ∈ f p.1) ∧ μ (s \ ⋃ p ∈ t, p.2) = 0

namespace VitaliFamily

variable {m0 : MeasurableSpace X} {μ : Measure X}

def mono (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ) : VitaliFamily ν where
  __ := v
  covering s f h h' :=
    let ⟨t, ts, disj, mem_f, hμ⟩ := v.covering s f h h'
    ⟨t, ts, disj, mem_f, hν hμ⟩

def FineSubfamilyOn (v : VitaliFamily μ) (f : X → Set (Set X)) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ ε > 0, ∃ t ∈ v.setsAt x ∩ f x, t ⊆ closedBall x ε

namespace FineSubfamilyOn

variable {v : VitaliFamily μ} {f : X → Set (Set X)} {s : Set X} (h : v.FineSubfamilyOn f s)

include h

theorem exists_disjoint_covering_ae :
    ∃ t : Set (X × Set X),
      (∀ p : X × Set X, p ∈ t → p.1 ∈ s) ∧
      (t.PairwiseDisjoint fun p => p.2) ∧
      (∀ p : X × Set X, p ∈ t → p.2 ∈ v.setsAt p.1 ∩ f p.1) ∧
      μ (s \ ⋃ (p : X × Set X) (_ : p ∈ t), p.2) = 0 :=
  v.covering s (fun x => v.setsAt x ∩ f x) (fun _ _ => inter_subset_left) h

protected def index : Set (X × Set X) :=
  h.exists_disjoint_covering_ae.choose
