/-
Extracted from RingTheory/Polynomial/Basic.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Ring-theoretic supplement of Algebra.Polynomial.

## Main results
* `MvPolynomial.isDomain`:
  If a ring is an integral domain, then so is its polynomial ring over finitely many variables.
* `Polynomial.isNoetherianRing`:
  Hilbert basis theorem, that if a ring is Noetherian then so is its polynomial ring.
-/

noncomputable section

open Polynomial

open Finset

universe u v w

variable {R : Type u} {S : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

-- INSTANCE (free from Core): instCharP

-- INSTANCE (free from Core): instExpChar

variable (R)

def degreeLE (n : WithBot ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ _ : ↑k > n, LinearMap.ker (lcoeff R k)

def degreeLT (n : ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ (_ : k ≥ n), LinearMap.ker (lcoeff R k)

variable {R}

theorem mem_degreeLE {n : WithBot ℕ} {f : R[X]} : f ∈ degreeLE R n ↔ degree f ≤ n := by
  simp only [degreeLE, Submodule.mem_iInf, degree_le_iff_coeff_zero, LinearMap.mem_ker]; rfl
