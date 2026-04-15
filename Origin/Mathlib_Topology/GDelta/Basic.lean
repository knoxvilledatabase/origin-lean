/-
Extracted from Topology/GDelta/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `Gδ` sets

In this file we define `Gδ` sets and prove their basic properties.

## Main definitions

* `IsGδ`: a set `s` is a `Gδ` set if it can be represented as an intersection
  of countably many open sets;

* `residual`: the σ-filter of residual sets. A set `s` is called *residual* if it includes a
  countable intersection of dense open sets.

* `IsNowhereDense`: a set is called *nowhere dense* iff its closure has empty interior
* `IsMeagre`: a set `s` is called *meagre* iff its complement is residual

## Main results

We prove that finite or countable intersections of Gδ sets are Gδ sets.

- `isClosed_isNowhereDense_iff_compl`: a closed set is nowhere dense iff
  its complement is open and dense
- `isMeagre_iff_countable_union_isNowhereDense`: a set is meagre iff it is contained in a countable
  union of nowhere dense sets
- subsets of meagre sets are meagre; countable unions of meagre sets are meagre

See `Mathlib/Topology/GDelta/MetrizableSpace.lean` for the proof that
continuity set of a function from a topological space to a metrizable space is a Gδ set.

## Tags

Gδ set, residual set, nowhere dense set, meagre set
-/

assert_not_exists UniformSpace

noncomputable section

open Topology TopologicalSpace Filter Encodable Set

variable {X Y ι : Type*} {ι' : Sort*}

section IsGδ

variable [TopologicalSpace X]

def IsGδ (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T

theorem IsOpen.isGδ {s : Set X} (h : IsOpen s) : IsGδ s :=
  ⟨{s}, by simp [h], countable_singleton _, (Set.sInter_singleton _).symm⟩
