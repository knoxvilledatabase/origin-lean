/-
Extracted from Analysis/Normed/Lp/Matrix.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matrices are isomorphic with linear maps between Lp spaces

This file provides a `WithLp` version of `Matrix.toLin'`.
-/

open Matrix ENNReal

variable {m n o R : Type*}

namespace Matrix

variable [Fintype n] [DecidableEq n] [CommRing R] (p q r : ℝ≥0∞)

open WithLp (toLp ofLp)

def toLpLin : Matrix m n R ≃ₗ[R] WithLp p (n → R) →ₗ[R] WithLp q (m → R) :=
  toLin' ≪≫ₗ
    (WithLp.linearEquiv _ R (n → R)).symm.arrowCongr
      (WithLp.linearEquiv _ R (m → R)).symm
