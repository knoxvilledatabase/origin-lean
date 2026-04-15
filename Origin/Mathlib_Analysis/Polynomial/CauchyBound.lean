/-
Extracted from Analysis/Polynomial/CauchyBound.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cauchy's bound on polynomial roots.

The bound is given by `Polynomial.cauchyBound`, which for `a_n x^n + a_(n-1) x^(n - 1) + ⋯ + a_0` is
`1 + max_(0 ≤ i < n) a_i / a_n`.

The theorem that this gives a bound to polynomial roots is `Polynomial.IsRoot.norm_lt_cauchyBound`.
-/

variable {K : Type*} [NormedDivisionRing K]

namespace Polynomial

open Finset NNReal

noncomputable def cauchyBound (p : K[X]) : ℝ≥0 :=
  sup (range p.natDegree) (‖p.coeff ·‖₊) / ‖p.leadingCoeff‖₊ + 1
