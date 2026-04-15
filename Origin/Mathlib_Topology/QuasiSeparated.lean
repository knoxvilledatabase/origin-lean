/-
Extracted from Topology/QuasiSeparated.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Quasi-separated spaces

A topological space is quasi-separated if the intersections of any pairs of compact open subsets
are still compact.
Notable examples include spectral spaces, Noetherian spaces, and Hausdorff spaces.

A non-example is the interval `[0, 1]` with doubled origin: the two copies of `[0, 1]` are compact
open subsets, but their intersection `(0, 1]` is not.

## Main results

- `IsQuasiSeparated`: A subset `s` of a topological space is quasi-separated if the intersections
  of any pairs of compact open subsets of `s` are still compact.
- `QuasiSeparatedSpace`: A topological space is quasi-separated if the intersections of any pairs
  of compact open subsets are still compact.
- `QuasiSeparatedSpace.of_isOpenEmbedding`: If `f : α → β` is an open embedding, and `β` is
  a quasi-separated space, then so is `α`.
-/

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

def IsQuasiSeparated (s : Set α) : Prop :=
  ∀ U V : Set α, U ⊆ s → IsOpen U → IsCompact U → V ⊆ s → IsOpen V → IsCompact V → IsCompact (U ∩ V)
