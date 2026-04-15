/-
Extracted from RingTheory/Complex.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Lemmas about `Algebra.trace` and `Algebra.norm` on `ℂ` -/

open Complex

theorem Algebra.leftMulMatrix_complex (z : ℂ) :
    Algebra.leftMulMatrix Complex.basisOneI z = !![z.re, -z.im; z.im, z.re] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, mul_re,
    mul_im, Matrix.of_apply]
  fin_cases j <;> dsimp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val]
  · simp only [one_re, mul_one, one_im, mul_zero,
      sub_zero, zero_add]
    fin_cases i <;> rfl
  · simp only [I_re, mul_zero, I_im,
      mul_one, zero_sub, add_zero]
    fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in

theorem Algebra.trace_complex_apply (z : ℂ) : Algebra.trace ℝ ℂ z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace Complex.basisOneI, Algebra.leftMulMatrix_complex,
    Matrix.trace_fin_two]
  exact (two_mul _).symm

set_option backward.isDefEq.respectTransparency false in

theorem Algebra.norm_complex_apply (z : ℂ) : Algebra.norm ℝ z = Complex.normSq z := by
  rw [Algebra.norm_eq_matrix_det Complex.basisOneI, Algebra.leftMulMatrix_complex,
    Matrix.det_fin_two, normSq_apply]
  simp

theorem Algebra.norm_complex_eq : Algebra.norm ℝ = normSq.toMonoidHom :=
  MonoidHom.ext Algebra.norm_complex_apply
