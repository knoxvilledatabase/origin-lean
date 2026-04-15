/-
Extracted from Analysis/Calculus/FDeriv/Pow.lean
Genuine: 4 of 10 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Fréchet Derivative of `f x ^ n`, `n : ℕ`

In this file we prove that the Fréchet derivative of `fun x => f x ^ n`,
where `n` is a natural number, is `n • f x ^ (n - 1)) • f'`.
Additionally, we prove the case for non-commutative rings (with primed names like `fderiv_pow'`),
where the result is instead `∑ i ∈ Finset.range n, f x ^ (n.pred - i) •> f' <• f x ^ i`.

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

## Keywords

derivative, power
-/

variable {𝕜 𝔸 E : Type*}

section NormedRing

variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAddCommGroup E]

variable [NormedAlgebra 𝕜 𝔸] [NormedSpace 𝕜 E] {f : E → 𝔸} {f' : E →L[𝕜] 𝔸} {x : E} {s : Set E}

open scoped RightActions

private theorem aux (f : E → 𝔸) (f' : E →L[𝕜] 𝔸) (x : E) (n : ℕ) :
    f x •> ∑ i ∈ Finset.range (n + 1), f x ^ ((n + 1).pred - i) •> f' <• f x ^ i
      + f' <• (f x ^ (n + 1)) =
    ∑ i ∈ Finset.range (n + 1 + 1), f x ^ ((n + 1 + 1).pred - i) •> f' <• f x ^ i := by
  rw [Finset.sum_range_succ _ (n + 1), Finset.smul_sum]
  simp only [Nat.pred_eq_sub_one, add_tsub_cancel_right, tsub_self, pow_zero, one_smul]
  simp_rw [smul_comm (_ : 𝔸) (_ : 𝔸ᵐᵒᵖ), smul_smul, ← pow_succ']
  congr! 5 with x hx
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hx
  rw [tsub_add_eq_add_tsub hx]

theorem hasStrictFDerivAt_pow' (n : ℕ) {x : 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ x ^ n)
      (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) x :=
  hasStrictFDerivAt_id _ |>.pow' n

theorem hasFDerivWithinAt_pow' (n : ℕ) {x : 𝔸} {s : Set 𝔸} :
    HasFDerivWithinAt (𝕜 := 𝕜) (fun x ↦ x ^ n)
      (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) s x :=
  hasFDerivWithinAt_id _ _ |>.pow' n

theorem hasFDerivAt_pow' (n : ℕ) {x : 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ x ^ n)
      (∑ i ∈ Finset.range n, x ^ (n.pred - i) •> ContinuousLinearMap.id 𝕜 _ <• x ^ i) x :=
  hasFDerivAt_id _ |>.pow' n
