/-
Extracted from Analysis/Normed/MulAction.lean
Genuine: 13 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.Algebra.UniformMulAction

/-!
# Lemmas for `BoundedSMul` over normed additive groups

Lemmas which hold only in `NormedSpace α β` are provided in another file.

Notably we prove that `NonUnitalSeminormedRing`s have bounded actions by left- and right-
multiplication. This allows downstream files to write general results about `BoundedSMul`, and then
deduce `const_mul` and `mul_const` results as an immediate corollary.
-/

variable {α β : Type*}

section SeminormedAddGroup

variable [SeminormedAddGroup α] [SeminormedAddGroup β] [SMulZeroClass α β]

variable [BoundedSMul α β]

@[bound]
theorem norm_smul_le (r : α) (x : β) : ‖r • x‖ ≤ ‖r‖ * ‖x‖ := by
  simpa [smul_zero] using dist_smul_pair r 0 x

@[bound]
theorem nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ ≤ ‖r‖₊ * ‖x‖₊ :=
  norm_smul_le _ _

theorem dist_smul_le (s : α) (x y : β) : dist (s • x) (s • y) ≤ ‖s‖ * dist x y := by
  simpa only [dist_eq_norm, sub_zero] using dist_smul_pair s x y

theorem nndist_smul_le (s : α) (x y : β) : nndist (s • x) (s • y) ≤ ‖s‖₊ * nndist x y :=
  dist_smul_le s x y

theorem lipschitzWith_smul (s : α) : LipschitzWith ‖s‖₊ (s • · : β → β) :=
  lipschitzWith_iff_dist_le_mul.2 <| dist_smul_le _

theorem edist_smul_le (s : α) (x y : β) : edist (s • x) (s • y) ≤ ‖s‖₊ • edist x y :=
  lipschitzWith_smul s x y

end SeminormedAddGroup

instance NonUnitalSeminormedRing.to_boundedSMul [NonUnitalSeminormedRing α] : BoundedSMul α α where
  dist_smul_pair' x y₁ y₂ := by simpa [mul_sub, dist_eq_norm] using norm_mul_le x (y₁ - y₂)
  dist_pair_smul' x₁ x₂ y := by simpa [sub_mul, dist_eq_norm] using norm_mul_le (x₁ - x₂) y

instance NonUnitalSeminormedRing.to_has_bounded_op_smul [NonUnitalSeminormedRing α] :
    BoundedSMul αᵐᵒᵖ α where
  dist_smul_pair' x y₁ y₂ := by
    simpa [sub_mul, dist_eq_norm, mul_comm] using norm_mul_le (y₁ - y₂) x.unop
  dist_pair_smul' x₁ x₂ y := by
    simpa [mul_sub, dist_eq_norm, mul_comm] using norm_mul_le y (x₁ - x₂).unop

section SeminormedRing

variable [SeminormedRing α] [SeminormedAddCommGroup β] [Module α β]

theorem BoundedSMul.of_norm_smul_le (h : ∀ (r : α) (x : β), ‖r • x‖ ≤ ‖r‖ * ‖x‖) :
    BoundedSMul α β :=
  { dist_smul_pair' := fun a b₁ b₂ => by simpa [smul_sub, dist_eq_norm] using h a (b₁ - b₂)
    dist_pair_smul' := fun a₁ a₂ b => by simpa [sub_smul, dist_eq_norm] using h (a₁ - a₂) b }

theorem BoundedSMul.of_nnnorm_smul_le (h : ∀ (r : α) (x : β), ‖r • x‖₊ ≤ ‖r‖₊ * ‖x‖₊) :
    BoundedSMul α β := .of_norm_smul_le h

end SeminormedRing

section NormedDivisionRing

variable [NormedDivisionRing α] [SeminormedAddGroup β]

variable [MulActionWithZero α β] [BoundedSMul α β]

theorem norm_smul (r : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖ := by
  by_cases h : r = 0
  · simp [h, zero_smul α x]
  · refine le_antisymm (norm_smul_le r x) ?_
    calc
      ‖r‖ * ‖x‖ = ‖r‖ * ‖r⁻¹ • r • x‖ := by rw [inv_smul_smul₀ h]
      _ ≤ ‖r‖ * (‖r⁻¹‖ * ‖r • x‖) := by gcongr; apply norm_smul_le
      _ = ‖r • x‖ := by rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (mt norm_eq_zero.1 h), one_mul]

theorem nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊ :=
  NNReal.eq <| norm_smul r x

end NormedDivisionRing

section NormedDivisionRingModule

variable [NormedDivisionRing α] [SeminormedAddCommGroup β]

variable [Module α β] [BoundedSMul α β]

theorem dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * dist x y := by
  simp_rw [dist_eq_norm, (norm_smul s (x - y)).symm, smul_sub]

theorem nndist_smul₀ (s : α) (x y : β) : nndist (s • x) (s • y) = ‖s‖₊ * nndist x y :=
  NNReal.eq <| dist_smul₀ s x y

theorem edist_smul₀ (s : α) (x y : β) : edist (s • x) (s • y) = ‖s‖₊ • edist x y := by
  simp only [edist_nndist, nndist_smul₀, ENNReal.coe_mul, ENNReal.smul_def, smul_eq_mul]

end NormedDivisionRingModule
