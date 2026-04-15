/-
Extracted from Topology/Compactification/StoneCech.lean
Genuine: 5 of 9 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-! # Stone-Čech compactification

Construction of the Stone-Čech compactification using ultrafilters.

For any topological space `α`, we build a compact Hausdorff space `StoneCech α` and a continuous
map `stoneCechUnit : α → StoneCech α` which is minimal in the sense of the following universal
property: for any compact Hausdorff space `β` and every map `f : α → β` such that
`hf : Continuous f`, there is a unique map `stoneCechExtend hf : StoneCech α → β` such that
`stoneCechExtend_extends : stoneCechExtend hf ∘ stoneCechUnit = f`.
Continuity of this extension is asserted by `continuous_stoneCechExtend` and uniqueness by
`stoneCech_hom_ext`.

Beware that the terminology “extend” is slightly misleading since `stoneCechUnit` is not always
injective, so one cannot always think of `α` as being “inside” its compactification `StoneCech α`.

## Implementation notes

Parts of the formalization are based on “Ultrafilters and Topology”
by Marius Stekelenburg, particularly section 5. However the construction in the general
case is different because the equivalence relation on spaces of ultrafilters described
by Stekelenburg causes issues with universes since it involves a condition
on all compact Hausdorff spaces. We replace it by a two steps construction.
The first step called `PreStoneCech` guarantees the expected universal property but
not the Hausdorff condition. We then define `StoneCech α` as `T2Quotient (PreStoneCech α)`.
-/

noncomputable section

open Filter Set

open Topology

universe u v

section Ultrafilter

def ultrafilterBasis (α : Type u) : Set (Set (Ultrafilter α)) :=
  range fun s : Set α ↦ { u | s ∈ u }

variable {α : Type u}

-- INSTANCE (free from Core): Ultrafilter.topologicalSpace

theorem ultrafilterBasis_is_basis : TopologicalSpace.IsTopologicalBasis (ultrafilterBasis α) :=
  ⟨by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩
    refine ⟨_, ⟨a ∩ b, rfl⟩, inter_mem ua ub, fun v hv ↦ ⟨?_, ?_⟩⟩ <;> apply mem_of_superset hv <;>
      simp [inter_subset_right],
    eq_univ_of_univ_subset <| subset_sUnion_of_mem <| ⟨univ, eq_univ_of_forall fun _ ↦ univ_mem⟩,
    rfl⟩

theorem ultrafilter_isOpen_basic (s : Set α) : IsOpen { u : Ultrafilter α | s ∈ u } :=
  ultrafilterBasis_is_basis.isOpen ⟨s, rfl⟩

theorem ultrafilter_isClosed_basic (s : Set α) : IsClosed { u : Ultrafilter α | s ∈ u } := by
  rw [← isOpen_compl_iff]
  convert ultrafilter_isOpen_basic sᶜ using 1
  ext u
  exact Ultrafilter.compl_mem_iff_notMem.symm

theorem ultrafilter_converges_iff {u : Ultrafilter (Ultrafilter α)} {x : Ultrafilter α} :
    ↑u ≤ 𝓝 x ↔ x = joinM u := by
  rw [eq_comm, ← Ultrafilter.coe_le_coe]
  change ↑u ≤ 𝓝 x ↔ ∀ s ∈ x, { v : Ultrafilter α | s ∈ v } ∈ u
  simp only [TopologicalSpace.nhds_generateFrom, le_iInf_iff, ultrafilterBasis, le_principal_iff,
    mem_setOf_eq]
  constructor
  · intro h a ha
    exact h _ ⟨ha, a, rfl⟩
  · rintro h a ⟨xi, a, rfl⟩
    exact h _ xi

-- INSTANCE (free from Core): ultrafilter_compact

-- INSTANCE (free from Core): Ultrafilter.t2Space

-- INSTANCE (free from Core): :
