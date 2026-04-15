/-
Extracted from Topology/Algebra/MvPolynomial.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Multivariate polynomials and continuity

In this file we prove the following lemma:

* `MvPolynomial.continuous_eval`: `MvPolynomial.eval` is continuous

## Tags

multivariate polynomial, continuity
-/

variable {X σ : Type*} [TopologicalSpace X] [CommSemiring X] [TopologicalSemiring X]
  (p : MvPolynomial σ X)

theorem MvPolynomial.continuous_eval : Continuous fun x ↦ eval x p := by
  continuity
