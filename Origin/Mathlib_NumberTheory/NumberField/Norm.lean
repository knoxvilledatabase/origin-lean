/-
Extracted from NumberTheory/NumberField/Norm.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Norm in number fields
Given a finite extension of number fields, we define the norm morphism as a function between the
rings of integers.

## Main definitions
* `RingOfIntegers.norm K` : `Algebra.norm` as a morphism `(𝓞 L) →* (𝓞 K)`.
## Main results
* `RingOfIntegers.dvd_norm` : if `L/K` is a finite Galois extension of fields, then, for all
  `(x : 𝓞 L)` we have that `x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x)`.

-/

open scoped NumberField

open Finset NumberField Algebra Module IntermediateField

section Rat

variable {K : Type*} [Field K] [NumberField K] (x : 𝓞 K)

theorem Algebra.coe_norm_int : (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : K) :=
  (Algebra.norm_localization (R := ℤ) (Rₘ := ℚ) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors ℤ) x).symm

theorem Algebra.coe_trace_int : (Algebra.trace ℤ _ x : ℚ) = Algebra.trace ℚ K (x : K) :=
  (Algebra.trace_localization (R := ℤ) (Rₘ := ℚ) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors ℤ) x).symm

end Rat

namespace RingOfIntegers

variable {L : Type*} (K : Type*) [Field K] [Field L] [Algebra K L]

noncomputable def norm : 𝓞 L →* 𝓞 K :=
  RingOfIntegers.restrict_monoidHom
    ((Algebra.norm K).comp (algebraMap (𝓞 L) L : (𝓞 L) →* L))
    fun x => isIntegral_norm K x.2
