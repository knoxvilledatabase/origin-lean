/-
Extracted from Topology/Algebra/MvPolynomial.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Multivariate polynomials and continuity

In this file we prove the following lemma:

* `MvPolynomial.continuous_eval`: `MvPolynomial.eval` is continuous

## Tags

multivariate polynomial, continuity
-/

variable {X σ : Type*} [TopologicalSpace X] [CommSemiring X] [IsTopologicalSemiring X]
  (p : MvPolynomial σ X)

theorem MvPolynomial.continuous_eval : Continuous fun x ↦ eval x p := by
  continuity
