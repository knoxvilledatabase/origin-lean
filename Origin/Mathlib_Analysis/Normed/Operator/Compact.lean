/-
Extracted from Analysis/Normed/Operator/Compact.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Compact operators

In this file we define compact linear operators between two topological vector spaces (TVS).

## Main definitions

* `IsCompactOperator` : predicate for compact operators

## Main statements

* `isCompactOperator_iff_isCompact_closure_image_ball` : the usual characterization of
  compact operators from a normed space to a T2 TVS.
* `IsCompactOperator.comp_clm` : precomposing a compact operator by a continuous linear map gives
  a compact operator
* `IsCompactOperator.clm_comp` : postcomposing a compact operator by a continuous linear map
  gives a compact operator
* `IsCompactOperator.continuous` : compact operators are automatically continuous
* `isClosed_setOf_isCompactOperator` : the set of compact operators is closed for the operator
  norm

## Implementation details

We define `IsCompactOperator` as a predicate, because the space of compact operators inherits all
of its structure from the space of continuous linear maps (e.g we want to have the usual operator
norm on compact operators).

The two natural options then would be to make it a predicate over linear maps or continuous linear
maps. Instead we define it as a predicate over bare functions, although it really only makes sense
for linear functions, because Lean is really good at finding coercions to bare functions (whereas
coercing from continuous linear maps to linear maps often needs type ascriptions).

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre 3][bourbaki2023]

## Tags

Compact operator
-/

open Function Set Filter Bornology Metric Pointwise Topology

def IsCompactOperator {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂]
    (f : M₁ → M₂) : Prop :=
  ∃ K, IsCompact K ∧ f ⁻¹' K ∈ (𝓝 0 : Filter M₁)

theorem isCompactOperator_zero {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁]
    [TopologicalSpace M₂] [Zero M₂] : IsCompactOperator (0 : M₁ → M₂) :=
  ⟨{0}, isCompact_singleton, mem_of_superset univ_mem fun _ _ => rfl⟩

theorem isCompactOperator_id_iff_locallyCompactSpace {E : Type*}
    [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] :
    IsCompactOperator (id : E → E) ↔ LocallyCompactSpace E :=
  ⟨fun ⟨_, hK, hK0⟩ ↦ hK.locallyCompactSpace_of_mem_nhds_of_addGroup hK0,
    fun _ ↦ exists_compact_mem_nhds 0⟩

alias ⟨LocallyCompactSpace.of_isCompactOperator_id, _⟩ :=

  isCompactOperator_id_iff_locallyCompactSpace
