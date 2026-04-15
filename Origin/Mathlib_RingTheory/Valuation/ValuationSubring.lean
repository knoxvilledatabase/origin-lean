/-
Extracted from RingTheory/Valuation/ValuationSubring.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Valuation subrings of a field

## Projects

The order structure on `ValuationSubring K`.

-/

universe u

noncomputable section

variable (K : Type u) [Field K]

structure ValuationSubring extends Subring K where
  mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier

namespace ValuationSubring

variable {K}

variable (A : ValuationSubring K)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

theorem mem_carrier (x : K) : x ∈ A.carrier ↔ x ∈ A := Iff.refl _
