/-
Extracted from Topology/ContinuousMap/Interval.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous bundled maps on intervals

In this file we prove a few results about `ContinuousMap` when the domain is an interval.
-/

open Set ContinuousMap Filter Topology

namespace ContinuousMap

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]

variable {a b c : α} [Fact (a ≤ b)] [Fact (b ≤ c)]

variable {E : Type*} [TopologicalSpace E]

def IccInclusionLeft : C(Icc a b, Icc a c) :=
  .inclusion <| Icc_subset_Icc le_rfl Fact.out

def IccInclusionRight : C(Icc b c, Icc a c) :=
  .inclusion <| Icc_subset_Icc Fact.out le_rfl

def projIccCM : C(α, Icc a b) :=
  ⟨projIcc a b Fact.out, continuous_projIcc⟩

def IccExtendCM : C(C(Icc a b, E), C(α, E)) where
  toFun f := f.comp projIccCM
  continuous_toFun := continuous_precomp projIccCM
