/-
Extracted from Algebra/QuaternionBasis.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basis on a quaternion-like algebra

## Main definitions

* `QuaternionAlgebra.Basis A c₁ c₂ c₃`: a basis for a subspace of an `R`-algebra `A` that has the
  same algebra structure as `ℍ[R,c₁,c₂,c₃]`.
* `QuaternionAlgebra.Basis.self R`: the canonical basis for `ℍ[R,c₁,c₂,c₃]`.
* `QuaternionAlgebra.Basis.compHom b f`: transform a basis `b` by an AlgHom `f`.
* `QuaternionAlgebra.lift`: Define an `AlgHom` out of `ℍ[R,c₁,c₂,c₃]` by its action on the basis
  elements `i`, `j`, and `k`. In essence, this is a universal property. Analogous to `Complex.lift`,
  but takes a bundled `QuaternionAlgebra.Basis` instead of just a `Subtype` as the amount of
  data / proofs is non-negligible.
-/

open Quaternion

namespace QuaternionAlgebra

structure Basis {R : Type*} (A : Type*) [CommRing R] [Ring A] [Algebra R A] (c₁ c₂ c₃ : R) where
  /-- The first imaginary unit -/
  i : A
  /-- The second imaginary unit -/
  j : A
  /-- The third imaginary unit -/
  k : A
  i_mul_i : i * i = c₁ • (1 : A) + c₂ • i
  j_mul_j : j * j = c₃ • (1 : A)
  i_mul_j : i * j = k
  j_mul_i : j * i = c₂ • j - k

initialize_simps_projections Basis

  (as_prefix i, as_prefix j, as_prefix k)

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

namespace Basis
