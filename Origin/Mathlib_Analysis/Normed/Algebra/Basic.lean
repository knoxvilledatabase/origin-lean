/-
Extracted from Analysis/Normed/Algebra/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Normed algebras

This file contains basic facts about normed algebras.

## Main results

* We show that the character space of a normed algebra is compact using the Banach-Alaoglu theorem.

## TODO

* Show compactness for topological vector spaces; this requires the TVS version of Banach-Alaoglu.

## Tags

normed algebra, character space, continuous functional calculus

-/

namespace IntermediateField

variable {K L : Type*} [NontriviallyNormedField K] [NormedField L] [NormedAlgebra K L]

-- INSTANCE (free from Core): (F

end IntermediateField

variable {𝕜 : Type*} {A : Type*}

namespace WeakDual

namespace CharacterSpace

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

theorem norm_le_norm_one (φ : characterSpace 𝕜 A) : ‖toStrongDual (φ : WeakDual 𝕜 A)‖ ≤ ‖(1 : A)‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (1 : A)) fun a =>
    mul_comm ‖a‖ ‖(1 : A)‖ ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ a)

-- INSTANCE (free from Core): [ProperSpace

end CharacterSpace

end WeakDual
