/-
Extracted from FieldTheory/KrullTopology.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Krull topology

We define the Krull topology on `Gal(L/K)` for an arbitrary field extension `L/K`. In order to do
this, we first define a `GroupFilterBasis` on `Gal(L/K)`, whose sets are `E.fixingSubgroup` for
all intermediate fields `E` with `E/K` finite dimensional.

## Main Definitions

- `finiteExts K L`. Given a field extension `L/K`, this is the set of intermediate fields that are
  finite-dimensional over `K`.

- `fixedByFinite K L`. Given a field extension `L/K`, `fixedByFinite K L` is the set of
  subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite

- `galBasis K L`. Given a field extension `L/K`, this is the filter basis on `Gal(L/K)` whose
  sets are `Gal(L/E)` for intermediate fields `E` with `E/K` finite.

- `galGroupBasis K L`. This is the same as `galBasis K L`, but with the added structure
  that it is a group filter basis on `Gal(L/K)`, rather than just a filter basis.

- `krullTopology K L`. Given a field extension `L/K`, this is the topology on `Gal(L/K)`, induced
  by the group filter basis `galGroupBasis K L`.

## Main Results

- `krullTopology_t2 K L`. For an integral field extension `L/K`, the topology `krullTopology K L`
  is Hausdorff.

- `krullTopology_isTotallySeparated K L`. For an integral field extension `L/K`, the topology
  `krullTopology K L` is totally separated.

- `stabilizer_isOpen_of_isIntegral`: For an integral field extension `L/K`, the stabilizer
  in `Gal(L/K)` of any element in `L` is open for the Krull topology.

- `IntermediateField.finrank_eq_fixingSubgroup_index`: given a Galois extension `K/k` and an
  intermediate field `L`, the `[L : k]` as a natural number is equal to the index of the
  fixing subgroup of `L`.

## Notation

- In docstrings, we will write `Gal(L/E)` to denote the fixing subgroup of an intermediate field
  `E`. That is, `Gal(L/E)` is the subgroup of `Gal(L/K)` consisting of automorphisms that fix
  every element of `E`. In particular, we distinguish between `Gal(L/E)` and `Gal(L/E)`, since the
  former is defined to be a subgroup of `Gal(L/K)`, while the latter is a group in its own right.

## Implementation Notes

- `krullTopology K L` is defined as an instance for type class inference.
-/

open scoped Pointwise

def finiteExts (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Set (IntermediateField K L) :=
  {E | FiniteDimensional K E}

def fixedByFinite (K L : Type*) [Field K] [Field L] [Algebra K L] : Set (Subgroup Gal(L/K)) :=
  IntermediateField.fixingSubgroup '' finiteExts K L

theorem top_fixedByFinite {K L : Type*} [Field K] [Field L] [Algebra K L] :
    ⊤ ∈ fixedByFinite K L :=
  ⟨⊥, IntermediateField.instFiniteSubtypeMemBot K, IntermediateField.fixingSubgroup_bot⟩

def galBasis (K L : Type*) [Field K] [Field L] [Algebra K L] : FilterBasis Gal(L/K) where
  sets := (fun g => g.carrier) '' fixedByFinite K L
  nonempty := ⟨⊤, ⊤, top_fixedByFinite, rfl⟩
  inter_sets := by
    rintro _ _ ⟨_, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨_, ⟨E2, h_E2, rfl⟩, rfl⟩
    have : FiniteDimensional K E1 := h_E1
    have : FiniteDimensional K E2 := h_E2
    refine ⟨(E1 ⊔ E2).fixingSubgroup.carrier, ⟨_, ⟨_, E1.finiteDimensional_sup E2, rfl⟩, rfl⟩, ?_⟩
    exact Set.subset_inter (E1.fixingSubgroup_le le_sup_left) (E2.fixingSubgroup_le le_sup_right)
