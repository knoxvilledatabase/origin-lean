/-
Extracted from Topology/NoetherianSpace.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Noetherian space

A Noetherian space is a topological space that satisfies any of the following equivalent conditions:
- `WellFounded ((· > ·) : TopologicalSpace.Opens α → TopologicalSpace.Opens α → Prop)`
- `WellFounded ((· < ·) : TopologicalSpace.Closeds α → TopologicalSpace.Closeds α → Prop)`
- `∀ s : Set α, IsCompact s`
- `∀ s : TopologicalSpace.Opens α, IsCompact s`

The first is chosen as the definition, and the equivalence is shown in
`TopologicalSpace.noetherianSpace_TFAE`.

Many examples of Noetherian spaces come from algebraic topology. For example, the underlying space
of a Noetherian scheme (e.g., the spectrum of a Noetherian ring) is Noetherian.

## Main Results

- `TopologicalSpace.NoetherianSpace.set`: Every subspace of a Noetherian space is Noetherian.
- `TopologicalSpace.NoetherianSpace.isCompact`: Every set in a Noetherian space is a compact set.
- `TopologicalSpace.noetherianSpace_TFAE`: Describes the equivalent definitions of Noetherian
  spaces.
- `TopologicalSpace.NoetherianSpace.range`: The image of a Noetherian space under a continuous map
  is Noetherian.
- `TopologicalSpace.NoetherianSpace.iUnion`: The finite union of Noetherian spaces is Noetherian.
- `TopologicalSpace.NoetherianSpace.discrete`: A Noetherian and Hausdorff space is discrete.
- `TopologicalSpace.NoetherianSpace.exists_finset_irreducible`: Every closed subset of a Noetherian
  space is a finite union of irreducible closed subsets.
- `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`: The number of irreducible
  components of a Noetherian space is finite.

-/

open Topology

variable (α β : Type*) [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

abbrev NoetherianSpace : Prop := WellFoundedGT (Opens α)

theorem noetherianSpace_iff_opens : NoetherianSpace α ↔ ∀ s : Opens α, IsCompact (s : Set α) := by
  rw [NoetherianSpace, CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact,
    CompleteLattice.isSupFiniteCompact_iff_all_elements_compact]
  exact forall_congr' Opens.isCompactElement_iff

-- INSTANCE (free from Core): (priority

variable {α β}

protected theorem NoetherianSpace.isCompact [NoetherianSpace α] (s : Set α) : IsCompact s := by
  refine isCompact_iff_finite_subcover.2 fun U hUo hs => ?_
  rcases ((noetherianSpace_iff_opens α).mp ‹_› ⟨⋃ i, U i, isOpen_iUnion hUo⟩).elim_finite_subcover U
    hUo Set.Subset.rfl with ⟨t, ht⟩
  exact ⟨t, hs.trans ht⟩

protected theorem _root_.Topology.IsInducing.noetherianSpace [NoetherianSpace α] {i : β → α}
    (hi : IsInducing i) : NoetherianSpace β :=
  (noetherianSpace_iff_opens _).2 fun _ => hi.isCompact_iff.2 (NoetherianSpace.isCompact _)
