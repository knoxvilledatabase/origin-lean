/-
Extracted from RingTheory/Polynomial/ScaleRoots.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Scaling the roots of a polynomial

This file defines `scaleRoots p s` for a polynomial `p` in one variable and a ring element `s` to
be the polynomial with root `r * s` for each root `r` of `p` and proves some basic results about it.
-/

variable {R S A K : Type*}

namespace Polynomial

section Semiring

variable [Semiring R] [Semiring S]

noncomputable def scaleRoots (p : R[X]) (s : R) : R[X] :=
  ∑ i ∈ p.support, monomial i (p.coeff i * s ^ (p.natDegree - i))
