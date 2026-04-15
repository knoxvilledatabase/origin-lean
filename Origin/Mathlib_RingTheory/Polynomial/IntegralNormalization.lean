/-
Extracted from RingTheory/Polynomial/IntegralNormalization.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Theory of monic polynomials

We define `integralNormalization`, which relate arbitrary polynomials to monic ones.
-/

open Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section IntegralNormalization

section Semiring

variable [Semiring R]

noncomputable def integralNormalization (p : R[X]) : R[X] :=
  p.sum fun i a ↦
    monomial i (if p.degree = i then 1 else a * p.leadingCoeff ^ (p.natDegree - 1 - i))
