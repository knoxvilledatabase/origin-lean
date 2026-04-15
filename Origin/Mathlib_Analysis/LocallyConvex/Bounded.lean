/-
Extracted from Analysis/LocallyConvex/Bounded.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Von Neumann Boundedness

This file defines natural or von Neumann bounded sets and proves elementary properties.

## Main declarations

* `Bornology.IsVonNBounded`: A set `s` is von Neumann-bounded if every neighborhood of zero
  absorbs `s`.
* `Bornology.vonNBornology`: The bornology made of the von Neumann-bounded sets.

## Main results

* `Bornology.IsVonNBounded.of_topologicalSpace_le`: A coarser topology admits more
  von Neumann-bounded sets.
* `Bornology.IsVonNBounded.image`: A continuous linear image of a bounded set is bounded.
* `Bornology.isVonNBounded_iff_smul_tendsto_zero`: Given any sequence `ε` of scalars which tends
  to `𝓝[≠] 0`, we have that a set `S` is bounded if and only if for any sequence `x : ℕ → S`,
  `ε • x` tends to 0. This shows that bounded sets are completely determined by sequences, which is
  the key fact for proving that sequential continuity implies continuity for linear maps defined on
  a bornological space

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

variable {𝕜 𝕜' E F ι : Type*}

open Set Filter Function

open scoped Topology Pointwise

namespace Bornology

section SeminormedRing

section Zero

variable (𝕜)

variable [SeminormedRing 𝕜] [SMul 𝕜 E] [Zero E]

variable [TopologicalSpace E]

def IsVonNBounded (s : Set E) : Prop :=
  ∀ ⦃V⦄, V ∈ 𝓝 (0 : E) → Absorbs 𝕜 V s

variable (E)
