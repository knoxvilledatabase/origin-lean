/-
Extracted from NumberTheory/ModularForms/EisensteinSeries/IsBoundedAtImInfty.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Boundedness of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are bounded at infinity.

## Outline of argument

We need to bound the value of the Eisenstein series (acted on by `A : SL(2,ℤ)`)
at a given point `z` in the upper half plane. Since these are modular forms of level `Γ(N)`,
it suffices to prove this for `z ∈ verticalStrip N z.im`.

We can then, first observe that the slash action just changes our `a` to `(a ᵥ* A)` and
we then use our bounds for Eisenstein series in these vertical strips to get the result.
-/

noncomputable section

open ModularForm UpperHalfPlane Matrix SlashInvariantForm CongruenceSubgroup

open scoped MatrixGroups

namespace EisensteinSeries

lemma summable_norm_eisSummand {k : ℤ} (hk : 3 ≤ k) (z : ℍ) :
    Summable fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖ := by
  have hk' : (2 : ℝ) < k := by norm_cast
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-k : ℝ)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro b
  simp only [eisSummand, norm_zpow]
  exact_mod_cast summand_bound z (show 0 ≤ (k : ℝ) by positivity) b

lemma norm_le_tsum_norm (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ) :
    ‖eisensteinSeries a k z‖ ≤ ∑' (x : Fin 2 → ℤ), ‖eisSummand k x z‖ := by
  simp_rw [eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ((summable_norm_eisSummand hk z).subtype _))
    (Summable.tsum_subtype_le (fun (x : Fin 2 → ℤ) ↦ ‖(eisSummand k x z)‖) _ (fun _ ↦ norm_nonneg _)
      (summable_norm_eisSummand hk z))

-- DISSOLVED: isBoundedAtImInfty_eisensteinSeriesSIF
