/-
Extracted from Data/Real/Sign.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Real sign function

This file introduces and contains some results about `Real.sign` which maps negative
real numbers to -1, positive real numbers to 1, and 0 to 0.

## Main definitions

* `Real.sign r` is $\begin{cases} -1 & \text{if } r < 0, \\
                              ~~\, 0 & \text{if } r = 0, \\
                              ~~\, 1 & \text{if } r > 0. \end{cases}$

## Tags

sign function
-/

namespace Real

noncomputable def sign (r : ℝ) : ℝ :=
  if r < 0 then -1 else if 0 < r then 1 else 0

theorem sign_of_neg {r : ℝ} (hr : r < 0) : sign r = -1 := by rw [sign, if_pos hr]

theorem sign_of_pos {r : ℝ} (hr : 0 < r) : sign r = 1 := by rw [sign, if_pos hr, if_neg hr.not_gt]
