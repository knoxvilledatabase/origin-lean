/-
Extracted from Analysis/Calculus/Deriv/Polynomial.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivatives of polynomials

In this file we prove that derivatives of polynomials in the analysis sense agree with their
derivatives in the algebraic sense.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## TODO

* Add results about multivariable polynomials.
* Generalize some (most?) results to an algebra over the base field.

## Keywords

derivative, polynomial
-/

universe u

open scoped Polynomial

open ContinuousLinearMap (smulRight)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

namespace Polynomial

/-! ### Derivative of a polynomial -/

variable {R : Type*} [CommSemiring R] [Algebra R 𝕜]

variable (p : 𝕜[X]) (q : R[X])

protected theorem hasStrictDerivAt (x : 𝕜) :
    HasStrictDerivAt (fun x => p.eval x) (p.derivative.eval x) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a => simpa [mul_assoc, derivative_monomial]
                      using (hasStrictDerivAt_pow n x).const_mul a

protected theorem hasStrictDerivAt_aeval (x : 𝕜) :
    HasStrictDerivAt (fun x => aeval x q) (aeval x (derivative q)) x := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).hasStrictDerivAt x

protected theorem hasDerivAt (x : 𝕜) : HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
  (p.hasStrictDerivAt x).hasDerivAt

protected theorem hasDerivAt_aeval (x : 𝕜) :
    HasDerivAt (fun x => aeval x q) (aeval x (derivative q)) x :=
  (q.hasStrictDerivAt_aeval x).hasDerivAt

protected theorem hasDerivWithinAt (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => p.eval x) (p.derivative.eval x) s x :=
  (p.hasDerivAt x).hasDerivWithinAt

protected theorem hasDerivWithinAt_aeval (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => aeval x q) (aeval x (derivative q)) s x :=
  (q.hasDerivAt_aeval x).hasDerivWithinAt

protected theorem differentiableAt : DifferentiableAt 𝕜 (fun x => p.eval x) x :=
  (p.hasDerivAt x).differentiableAt

protected theorem differentiableAt_aeval : DifferentiableAt 𝕜 (fun x => aeval x q) x :=
  (q.hasDerivAt_aeval x).differentiableAt

protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 (fun x => p.eval x) s x :=
  p.differentiableAt.differentiableWithinAt

protected theorem differentiableWithinAt_aeval :
    DifferentiableWithinAt 𝕜 (fun x => aeval x q) s x :=
  q.differentiableAt_aeval.differentiableWithinAt
