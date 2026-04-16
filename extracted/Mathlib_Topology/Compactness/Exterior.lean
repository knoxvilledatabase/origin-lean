/-
Extracted from Topology/Compactness/Exterior.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.Peel
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Exterior

noncomputable section

/-!
# Compactness of the exterior of a set

In this file we prove that the exterior of a set
(defined as the intersection of all of its neighborhoods)
is a compact set if and only if the original set is a compact set.
-/

variable {X : Type*} [TopologicalSpace X] {s : Set X}

theorem IsCompact.exterior_iff : IsCompact (exterior s) ↔ IsCompact s := by
  simp only [isCompact_iff_finite_subcover]
  peel with ι U hUo
  simp only [(isOpen_iUnion hUo).exterior_subset,
    (isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hUo i).exterior_subset]

protected alias ⟨IsCompact.of_exterior, IsCompact.exterior⟩ := IsCompact.exterior_iff

lemma Set.Finite.isCompact_exterior (hs : s.Finite) : IsCompact (exterior s) :=
  hs.isCompact.exterior
