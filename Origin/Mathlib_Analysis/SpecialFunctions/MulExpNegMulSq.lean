/-
Extracted from Analysis/SpecialFunctions/MulExpNegMulSq.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Definition of `mulExpNegMulSq` and properties

`mulExpNegMulSq` is the mapping `fun (ε : ℝ) (x : ℝ) => x * Real.exp (- (ε * x * x))`. By
composition, it can be used to transform a function `g : E → ℝ` into a bounded function
`mulExpNegMulSq ε ∘ g : E → ℝ = fun x => g x * Real.exp (-ε * g x * g x)` with useful
boundedness and convergence properties.

## Main Properties

- `abs_mulExpNegMulSq_le`: For fixed `ε > 0`, the mapping `x ↦ mulExpNegMulSq ε x` is
  bounded by `Real.sqrt ε⁻¹`;
- `tendsto_mulExpNegMulSq`: For fixed `x : ℝ`, the mapping `mulExpNegMulSq ε x`
  converges pointwise to `x` as `ε → 0`;
- `lipschitzWith_one_mulExpNegMulSq`: For fixed `ε > 0`, the mapping `mulExpNegMulSq ε` is
  Lipschitz with constant `1`;
- `abs_mulExpNegMulSq_comp_le_norm`: For a fixed bounded continuous function `g`, the mapping
  `mulExpNegMulSq ε ∘ g` is bounded by `norm g`, uniformly in `ε ≥ 0`;
-/

open NNReal ENNReal BoundedContinuousFunction Filter

open scoped Topology

namespace Real

/-! ### Definition and properties of `fun x => x * Real.exp (- (ε * x * x))` -/

noncomputable

def mulExpNegMulSq (ε x : ℝ) := x * exp (-(ε * x * x))

theorem neg_mulExpNegMulSq_neg (ε x : ℝ) : - mulExpNegMulSq ε (-x) = mulExpNegMulSq ε x := by
  simp [mulExpNegMulSq]

theorem mulExpNegMulSq_one_le_one (x : ℝ) : mulExpNegMulSq 1 x ≤ 1 := by
  simp only [mulExpNegMulSq, one_mul]
  rw [← le_div_iff₀ (exp_pos (-(x * x))), exp_neg, div_inv_eq_mul, one_mul]
  apply le_trans _ (add_one_le_exp (x * x))
  nlinarith

theorem neg_one_le_mulExpNegMulSq_one (x : ℝ) : -1 ≤ mulExpNegMulSq 1 x := by
  rw [← neg_mulExpNegMulSq_neg, neg_le_neg_iff]
  exact mulExpNegMulSq_one_le_one (-x)

theorem abs_mulExpNegMulSq_one_le_one (x : ℝ) : |mulExpNegMulSq 1 x| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_mulExpNegMulSq_one x, mulExpNegMulSq_one_le_one x⟩

variable {ε : ℝ}
