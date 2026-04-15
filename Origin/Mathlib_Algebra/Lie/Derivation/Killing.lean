/-
Extracted from Algebra/Lie/Derivation/Killing.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivations of finite-dimensional Killing Lie algebras

This file establishes that all derivations of finite-dimensional Killing Lie algebras are inner.

## Main statements

- `LieDerivation.Killing.ad_mem_orthogonal_of_mem_orthogonal`: if a derivation `D` is in the Killing
  orthogonal of the range of the adjoint action, then, for any `x : L`, `ad (D x)` is also in this
  orthogonal.
- `LieDerivation.Killing.range_ad_eq_top`: in a finite-dimensional Lie algebra with non-degenerate
  Killing form, the range of the adjoint action is full,
- `LieDerivation.Killing.exists_eq_ad`: in a finite-dimensional Lie algebra with non-degenerate
  Killing form, any derivation is an inner derivation.
-/

namespace LieDerivation.IsKilling

variable (R L : Type*) [Field R] [LieRing L] [LieAlgebra R L]

local notation "𝔻" => (LieDerivation R L L)

local notation "𝕀" => (LieHom.range (ad R L))

local notation "𝕀ᗮ" => LinearMap.BilinForm.orthogonal (killingForm R 𝔻) 𝕀

lemma killingForm_restrict_range_ad [Module.Finite R L] :
    (killingForm R 𝔻).restrict 𝕀 = killingForm R 𝕀 := by
  rw [← (ad_isIdealMorphism R L).eq, ← LieIdeal.killingForm_eq]
  rfl
