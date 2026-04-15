/-
Extracted from NumberTheory/NumberField/FractionalIdeal.lean
Genuine: 6 of 9 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# Fractional ideals of number fields

Prove some results on the fractional ideals of number fields.

## Main definitions and results

* `NumberField.basisOfFractionalIdeal`: A `ℚ`-basis of `K` that spans `I` over `ℤ` where `I` is
  a fractional ideal of a number field `K`.
* `NumberField.det_basisOfFractionalIdeal_eq_absNorm`: for `I` a fractional ideal of a number
  field `K`, the absolute value of the determinant of the base change from `integralBasis` to
  `basisOfFractionalIdeal I` is equal to the norm of `I`.
-/

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

open scoped nonZeroDivisors

section Basis

open Module

-- INSTANCE (free from Core): (I

-- INSTANCE (free from Core): (I

-- INSTANCE (free from Core): (I

noncomputable def fractionalIdealBasis (I : FractionalIdeal (𝓞 K)⁰ K) :
    Basis (Free.ChooseBasisIndex ℤ I) ℤ I := Free.chooseBasis ℤ I

noncomputable def basisOfFractionalIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Free.ChooseBasisIndex ℤ I) ℚ K :=
  (fractionalIdealBasis K I.1).ofIsLocalizedModule ℚ ℤ⁰
    ((Submodule.subtype (I : Submodule (𝓞 K) K)).restrictScalars ℤ)

theorem basisOfFractionalIdeal_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    basisOfFractionalIdeal K I i = fractionalIdealBasis K I.1 i :=
  (fractionalIdealBasis K I.1).ofIsLocalizedModule_apply ℚ ℤ⁰ _ i

theorem mem_span_basisOfFractionalIdeal {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : K} :
    x ∈ Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) ↔ x ∈ (I : Set K) := by
  rw [basisOfFractionalIdeal, (fractionalIdealBasis K I.1).ofIsLocalizedModule_span ℚ ℤ⁰ _]
  simp

open Module in

theorem fractionalIdeal_rank (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    finrank ℤ I = finrank ℤ (𝓞 K) := by
  rw [finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank,
    finrank_eq_card_basis (basisOfFractionalIdeal K I)]

end Basis

section Norm

open Module

theorem det_basisOfFractionalIdeal_eq_absNorm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (e : (Free.ChooseBasisIndex ℤ (𝓞 K)) ≃ (Free.ChooseBasisIndex ℤ I)) :
    |(integralBasis K).det ((basisOfFractionalIdeal K I).reindex e.symm)| =
      FractionalIdeal.absNorm I.1 := by
  rw [← FractionalIdeal.abs_det_basis_change (RingOfIntegers.basis K) I.1
    ((fractionalIdealBasis K I.1).reindex e.symm)]
  congr
  ext
  simpa using basisOfFractionalIdeal_apply K I _

end Norm

end NumberField
