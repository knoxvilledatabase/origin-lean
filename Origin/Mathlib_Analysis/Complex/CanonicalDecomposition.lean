/-
Extracted from Analysis/Complex/CanonicalDecomposition.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Canonical Decomposition

If a function `f` is meromorphic on a compact set `U`, then it has only finitely many zeros and
poles on the disk, and the theorem `MeromorphicOn.extract_zeros_poles` can be used to re-write `f`
as `(∏ᶠ u, (· - u) ^ divisor f U u) • g`, where `g` is analytic without zeros on `U`. In case where
`U` is a disk, one consider a similar decomposition, called *Canonical Decomposition* or *Blaschke
Product* that replaces the factors `(· - u)` by canonical factors that take only values of norm
one on the boundary of the circle. This file introduces the canonical factors.

See Page 160f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.

TODO: Formulate the canonical decomposition.
-/

namespace Complex

open ComplexConjugate Metric Real

variable {R : ℝ} {w : ℂ}

/-!
## Canonical Factors

Given `R : ℝ` and `w : ℂ`, the Blaschke factor `Blaschke R w : ℂ → ℂ` is meromorphic in normal form,
has a single pole at `w`, no zeros, and takes values of norm one on the circle of radius `R`.
-/

noncomputable def canonicalFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))
