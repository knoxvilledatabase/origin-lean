/-
Extracted from NumberTheory/ModularForms/EisensteinSeries/Summable.lean
Genuine: 18 of 20 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Summability of Eisenstein series

We gather results about the summability of Eisenstein series, particularly
the summability of the Eisenstein series summands, which are used in the proof of the
boundedness of Eisenstein series at infinity.
-/

noncomputable section

open Complex UpperHalfPlane Set Finset Topology Filter Asymptotics

open scoped UpperHalfPlane Topology Nat

variable (z : ℍ)

namespace EisensteinSeries

lemma norm_eq_max_natAbs (x : Fin 2 → ℤ) : ‖x‖ = max (x 0).natAbs (x 1).natAbs := by
  rw [← coe_nnnorm, ← NNReal.coe_natCast, NNReal.coe_inj, Nat.cast_max]
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp only [pi_nnnorm_le_iff, Fin.forall_fin_two, max_le_iff, NNReal.natCast_natAbs]

lemma norm_symm (x y : ℤ) : ‖![x, y]‖ = ‖![y, x]‖ := by
  simp [EisensteinSeries.norm_eq_max_natAbs, max_comm]

theorem abs_le_left_of_norm (m n : ℤ) : |n| ≤ ‖![n, m]‖ := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  left
  rw [Int.abs_eq_natAbs]
  exact le_refl _

theorem abs_le_right_of_norm (m n : ℤ) : |m| ≤ ‖![n, m]‖ := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  right
  rw [Int.abs_eq_natAbs]
  exact le_refl _

lemma abs_norm_eq_max_natAbs (n : ℕ) : ‖![1, (n + 1 : ℤ)]‖ = n + 1 := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

lemma abs_norm_eq_max_natAbs_neg (n : ℕ) : ‖![1, -(n + 1 : ℤ)]‖ = n + 1 := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

section bounding_functions

def r1 : ℝ := z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)

lemma r1_eq : r1 z = 1 / ((z.re / z.im) ^ 2 + 1) := by
  rw [div_pow, div_add_one (by positivity), one_div_div, r1]

lemma r1_pos : 0 < r1 z := by
  dsimp only [r1]
  positivity

lemma r1_aux_bound (c : ℝ) {d : ℝ} (hd : 1 ≤ d ^ 2) :
    r1 z ≤ (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
  have H1 : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 =
    c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2 := by ring
  have H2 : (c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2) * (z.re ^ 2 + z.im ^ 2)
    - z.im ^ 2 = (c * (z.re ^ 2 + z.im ^ 2) + d * z.re) ^ 2 + (d ^ 2 - 1) * z.im ^ 2 := by ring
  rw [r1, H1, div_le_iff₀ (by positivity), ← sub_nonneg, H2]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg _))

def r : ℝ := min z.im √(r1 z)

lemma r_pos : 0 < r z := by
  simp only [r, lt_min_iff, im_pos, Real.sqrt_pos, r1_pos, and_self]

lemma r_lower_bound_on_verticalStrip {A B : ℝ} (h : 0 < B) (hz : z ∈ verticalStrip A B) :
    r ⟨⟨A, B⟩, h⟩ ≤ r z := by
  apply min_le_min hz.2
  gcongr
  simp only [r1_eq, div_pow, one_div]
  rw [inv_le_inv₀ (by positivity) (by positivity), add_le_add_iff_right, ← even_two.pow_abs]
  gcongr
  exacts [hz.1, hz.2]

lemma auxbound1 {c : ℝ} (d : ℝ) (hc : 1 ≤ c ^ 2) : r z ≤ ‖c * (z : ℂ) + d‖ := by
  rcases z with ⟨z, hz⟩
  have H1 : z.im ≤ √((c * z.re + d) ^ 2 + (c * z).im ^ 2) := by
    rw [Real.le_sqrt' hz, im_ofReal_mul, mul_pow]
    exact (le_mul_of_one_le_left (sq_nonneg _) hc).trans <| le_add_of_nonneg_left (sq_nonneg _)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ← pow_two, add_im, mul_im,
    coe_im, ofReal_im, zero_mul, add_zero, min_le_iff] using Or.inl H1

lemma auxbound2 (c : ℝ) {d : ℝ} (hd : 1 ≤ d ^ 2) : r z ≤ ‖c * (z : ℂ) + d‖ := by
  have H1 : √(r1 z) ≤ √((c * z.re + d) ^ 2 + (c * z.im) ^ 2) :=
    (Real.sqrt_le_sqrt_iff (by positivity)).mpr (r1_aux_bound _ _ hd)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ofReal_re, ← pow_two,
    add_im, im_ofReal_mul, coe_im, ofReal_im, add_zero, min_le_iff] using Or.inr H1

-- DISSOLVED: div_max_sq_ge_one

-- DISSOLVED: r_mul_max_le

lemma summand_bound {k : ℝ} (hk : 0 ≤ k) (x : Fin 2 → ℤ) :
    ‖x 0 * (z : ℂ) + x 1‖ ^ (-k) ≤ (r z) ^ (-k) * ‖x‖ ^ (-k) := by
  by_cases hx : x = 0
  · simp only [hx, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, norm_zero]
    by_cases h : -k = 0
    · rw [h, Real.rpow_zero, Real.rpow_zero, one_mul]
    · rw [Real.zero_rpow h, mul_zero]
  · rw [← Real.mul_rpow (r_pos _).le (norm_nonneg _)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos (r_pos _) (norm_pos_iff.mpr hx)) (r_mul_max_le z hx)
      (neg_nonpos.mpr hk)

variable {z} in

lemma summand_bound_of_mem_verticalStrip {k : ℝ} (hk : 0 ≤ k) (x : Fin 2 → ℤ)
    {A B : ℝ} (hB : 0 < B) (hz : z ∈ verticalStrip A B) :
    ‖x 0 * (z : ℂ) + x 1‖ ^ (-k) ≤ r ⟨⟨A, B⟩, hB⟩ ^ (-k) * ‖x‖ ^ (-k) := by
  refine (summand_bound z hk x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Real.rpow_le_rpow_of_nonpos (r_pos _) (r_lower_bound_on_verticalStrip z hB hz)
    (neg_nonpos.mpr hk)

lemma linear_isTheta_right_add (c e : ℤ) (z : ℂ) :
    (fun d : ℤ ↦ c * z + d + e) =Θ[cofinite] fun n ↦ (n : ℝ) := by
  apply IsTheta.add_isLittleO <;>
  [refine Asymptotics.IsLittleO.add_isTheta ?_ (Int.cast_complex_isTheta_cast_real); skip] <;>
  simpa [-Int.cofinite_eq] using
    .inr <| tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real
