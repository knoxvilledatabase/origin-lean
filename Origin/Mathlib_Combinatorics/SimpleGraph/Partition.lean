/-
Extracted from Combinatorics/SimpleGraph/Partition.lean
Genuine: 12 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Graph partitions

This module provides an interface for dealing with partitions on simple graphs. A partition of
a graph `G`, with vertices `V`, is a set `P` of disjoint nonempty subsets of `V` such that:

* The union of the subsets in `P` is `V`.

* Each element of `P` is an independent set. (Each subset contains no pair of adjacent vertices.)

Graph partitions are graph colorings that do not name their colors.  They are adjoint in the
following sense. Given a graph coloring, there is an associated partition from the set of color
classes, and given a partition, there is an associated graph coloring from using the partition's
subsets as colors.  Going from graph colorings to partitions and back makes a coloring "canonical":
all colors are given a canonical name and unused colors are removed.  Going from partitions to
graph colorings and back is the identity.

## Main definitions

* `SimpleGraph.Partition` is a structure to represent a partition of a simple graph

* `SimpleGraph.Partition.PartsCardLe` is whether a given partition is an `n`-partition.
  (a partition with at most `n` parts).

* `SimpleGraph.Partitionable n` is whether a given graph is `n`-partite

* `SimpleGraph.Partition.toColoring` creates colorings from partitions

* `SimpleGraph.Coloring.toPartition` creates partitions from colorings

## Main statements

* `SimpleGraph.partitionable_iff_colorable` is that `n`-partitionability and
  `n`-colorability are equivalent.

-/

universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

structure Partition where
  /-- `parts`: a set of subsets of the vertices `V` of `G`. -/
  parts : Set (Set V)
  /-- `isPartition`: a proof that `parts` is a proper partition of `V`. -/
  isPartition : Setoid.IsPartition parts
  /-- `independent`: a proof that each element of `parts` doesn't have a pair of adjacent vertices.

-/

  independent : ∀ s ∈ parts, IsAntichain G.Adj s

def Partition.PartsCardLe {G : SimpleGraph V} (P : G.Partition) (n : ℕ) : Prop :=
  ∃ h : P.parts.Finite, h.toFinset.card ≤ n

def Partitionable (n : ℕ) : Prop := ∃ P : G.Partition, P.PartsCardLe n

namespace Partition

variable {G}

variable (P : G.Partition)

def partOfVertex (v : V) : Set V := Classical.choose (P.isPartition.2 v)

theorem partOfVertex_mem (v : V) : P.partOfVertex v ∈ P.parts := by
  obtain ⟨h, -⟩ := (P.isPartition.2 v).choose_spec.1
  exact h

theorem mem_partOfVertex (v : V) : v ∈ P.partOfVertex v := by
  obtain ⟨⟨_, h⟩, _⟩ := (P.isPartition.2 v).choose_spec
  exact h

theorem partOfVertex_ne_of_adj {v w : V} (h : G.Adj v w) : P.partOfVertex v ≠ P.partOfVertex w := by
  intro hn
  have hw := P.mem_partOfVertex w
  rw [← hn] at hw
  exact P.independent _ (P.partOfVertex_mem v) (P.mem_partOfVertex v) hw (G.ne_of_adj h) h

def toColoring : G.Coloring P.parts :=
  Coloring.mk (fun v ↦ ⟨P.partOfVertex v, P.partOfVertex_mem v⟩) fun hvw ↦ by
    rw [Ne, Subtype.mk_eq_mk]
    exact P.partOfVertex_ne_of_adj hvw

def toColoring' : G.Coloring (Set V) :=
  Coloring.mk P.partOfVertex fun hvw ↦ P.partOfVertex_ne_of_adj hvw

theorem colorable [Fintype P.parts] : G.Colorable (Fintype.card P.parts) :=
  P.toColoring.colorable

end Partition

variable {G}

@[simps]
def Coloring.toPartition {α : Type v} (C : G.Coloring α) : G.Partition where
  parts := C.colorClasses
  isPartition := C.colorClasses_isPartition
  independent := by
    rintro s ⟨c, rfl⟩
    apply C.color_classes_independent

@[simps]
instance : Inhabited (Partition G) := ⟨G.selfColoring.toPartition⟩

theorem partitionable_iff_colorable {n : ℕ} : G.Partitionable n ↔ G.Colorable n := by
  constructor
  · rintro ⟨P, hf, hc⟩
    have : Fintype P.parts := hf.fintype
    rw [Set.Finite.card_toFinset hf] at hc
    apply P.colorable.mono hc
  · rintro ⟨C⟩
    refine ⟨C.toPartition, C.colorClasses_finite, le_trans ?_ (Fintype.card_fin n).le⟩
    generalize_proofs h
    change Set.Finite (Coloring.colorClasses C) at h
    have : Fintype C.colorClasses := C.colorClasses_finite.fintype
    rw [h.card_toFinset]
    exact C.card_colorClasses_le

end SimpleGraph
