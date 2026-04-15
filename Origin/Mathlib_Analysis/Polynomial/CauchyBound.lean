/-
Extracted from Analysis/Polynomial/CauchyBound.lean
Genuine: 8 | Conflates: 0 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Cauchy's bound on polynomial roots.

The bound is given by `Polynomial.cauchyBound`, which for `a_n x^n + a_(n-1) x^(n - 1) + ⋯ + a_0` is
is `1 + max_(0 ≤ i < n) a_i / a_n`.

The theorem that this gives a bound to polynomial roots is `Polynomial.IsRoot.norm_lt_cauchyBound`.
-/

variable {K : Type*} [NormedDivisionRing K]

namespace Polynomial

open Finset NNReal

noncomputable def cauchyBound (p : K[X]) : ℝ≥0 :=
  sup (range p.natDegree) (‖p.coeff ·‖₊) / ‖p.leadingCoeff‖₊ + 1

@[simp]
lemma one_le_cauchyBound (p : K[X]) : 1 ≤ cauchyBound p := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_zero : cauchyBound (0 : K[X]) = 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_C (x : K) : cauchyBound (C x) = 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_one : cauchyBound (1 : K[X]) = 1 := cauchyBound_C 1

@[simp]
lemma cauchyBound_X : cauchyBound (X : K[X]) = 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_X_add_C (x : K) : cauchyBound (X + C x) = ‖x‖₊ + 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_X_sub_C (x : K) : cauchyBound (X - C x) = ‖x‖₊ + 1 := by
  simp [cauchyBound]

-- DISSOLVED: cauchyBound_smul

-- DISSOLVED: IsRoot.norm_lt_cauchyBound

end Polynomial
