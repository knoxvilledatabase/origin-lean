/-
Extracted from NumberTheory/NumberField/DedekindZeta.lean
Genuine: 4 of 6 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# The Dedekind zeta function of a number field

In this file, we define and prove results about the Dedekind zeta function of a number field.

## Main definitions and results

* `NumberField.dedekindZeta`: the Dedekind zeta function.
* `NumberField.dedekindZeta_residue`: the value of the residue at `s = 1` of the Dedekind
  zeta function.
* `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`: **Dirichlet class number formula**
  computation of the residue of the Dedekind zeta function at `s = 1`, see Chap. 7 of
  [D. Marcus, *Number Fields*][marcus1977number]

## TODO

Generalize the construction of the Dedekind zeta function.
-/

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

open Filter Ideal NumberField.InfinitePlace NumberField.Units Topology nonZeroDivisors

namespace NumberField

open scoped Real

def dedekindZeta (s : ℂ) :=
  LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

def dedekindZeta_residue : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
    (torsionOrder K * Real.sqrt |discr K|)

theorem dedekindZeta_residue_pos : 0 < dedekindZeta_residue K := by
  refine div_pos ?_ ?_
  · exact mul_pos (mul_pos (by positivity) (regulator_pos K)) (Nat.cast_pos.mpr (classNumber_pos K))
  · exact mul_pos (Nat.cast_pos.mpr (torsionOrder_pos K)) <|
      Real.sqrt_pos_of_pos <| abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

-- DISSOLVED: dedekindZeta_residue_ne_zero

theorem tendsto_sub_one_mul_dedekindZeta_nhdsGT :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) := by
  refine LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg _ ?_
    (fun _ ↦ Nat.cast_nonneg _)
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

end NumberField
