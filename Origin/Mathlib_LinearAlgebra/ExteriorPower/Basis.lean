/-
Extracted from LinearAlgebra/ExteriorPower/Basis.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Constructs a basis for exterior powers
-/

variable {R K M E : Type*} {n : ℕ}
  [CommRing R] [Field K] [AddCommGroup M] [Module R M] [AddCommGroup E] [Module K E]

open BigOperators

namespace exteriorPower

/-! Finiteness of the exterior power. -/

-- INSTANCE (free from Core): instFinite

/-! We construct a basis of `⋀[R]^n M` from a basis of `M`. -/

open Module Set Set.powersetCard

variable (R n)

noncomputable def ιMultiDual {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) : Module.Dual R (⋀[R]^n M) :=
  pairingDual R M n (ιMulti_family R n b.coord s)
