/-
Extracted from RingTheory/OreLocalization/NonZeroDivisors.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Ore Localization over nonZeroDivisors in monoids with zeros.
-/

open scoped nonZeroDivisors

namespace OreLocalization

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] {S : Submonoid R} [OreSet S]

theorem nontrivial_of_nonZeroDivisorsLeft [Nontrivial R] (hS : S ≤ nonZeroDivisorsLeft R) :
    Nontrivial R[S⁻¹] :=
  nontrivial_iff.mpr (fun e ↦ one_ne_zero <| hS e 1 (zero_mul _))

theorem nontrivial_of_nonZeroDivisorsRight [Nontrivial R] (hS : S ≤ nonZeroDivisorsRight R) :
    Nontrivial R[S⁻¹] :=
  nontrivial_iff.mpr (fun e ↦ one_ne_zero <| hS e 1 (mul_zero _))

theorem nontrivial_of_nonZeroDivisors [Nontrivial R] (hS : S ≤ R⁰) :
    Nontrivial R[S⁻¹] :=
  nontrivial_of_nonZeroDivisorsLeft (hS.trans inf_le_left)

variable [Nontrivial R] [OreSet R⁰]

-- INSTANCE (free from Core): nontrivial

variable [NoZeroDivisors R]

open Classical in
