/-
Extracted from Algebra/Lie/Normalizer.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The normalizer of Lie submodules and subalgebras.

Given a Lie module `M` over a Lie subalgebra `L`, the normalizer of a Lie submodule `N ⊆ M` is
the Lie submodule with underlying set `{ m | ∀ (x : L), ⁅x, m⁆ ∈ N }`.

The lattice of Lie submodules thus has two natural operations, the normalizer: `N ↦ N.normalizer`
and the ideal operation: `N ↦ ⁅⊤, N⁆`; these are adjoint, i.e., they form a Galois connection. This
adjointness is the reason that we may define nilpotency in terms of either the upper or lower
central series.

Given a Lie subalgebra `H ⊆ L`, we may regard `H` as a Lie submodule of `L` over `H`, and thus
consider the normalizer. This turns out to be a Lie subalgebra.

## Main definitions

  * `LieSubmodule.normalizer`
  * `LieSubalgebra.normalizer`
  * `LieSubmodule.gc_top_lie_normalizer`

## Tags

lie algebra, normalizer
-/

variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

namespace LieSubmodule

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

def normalizer : LieSubmodule R L M where
  carrier := {m | ∀ x : L, ⁅x, m⁆ ∈ N}
  add_mem' hm₁ hm₂ x := by rw [lie_add]; exact N.add_mem' (hm₁ x) (hm₂ x)
  zero_mem' x := by simp
  smul_mem' t m hm x := by rw [lie_smul]; exact N.smul_mem' t (hm x)
  lie_mem {x m} hm y := by rw [leibniz_lie]; exact N.add_mem' (hm ⁅y, x⁆) (N.lie_mem (hm y))
