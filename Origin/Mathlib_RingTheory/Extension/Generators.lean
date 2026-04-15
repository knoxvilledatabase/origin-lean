/-
Extracted from RingTheory/Extension/Generators.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Generators of algebras

## Main definition

- `Algebra.Generators`: A family of generators of an `R`-algebra `S` consists of
  1. `vars`: The type of variables.
  2. `val : vars → S`: The assignment of each variable to a value.
  3. `σ`: A set-theoretic section of the induced `R`-algebra homomorphism `R[X] → S`, where we
     write `R[X]` for `R[vars]`.

- `Algebra.Generators.Hom`: Given a commuting square
  ```
  R --→ P = R[X] ---→ S
  |                   |
  ↓                   ↓
  R' -→ P' = R'[X'] → S
  ```
  A hom between `P` and `P'` is an assignment `X → P'` such that the arrows commute.

- `Algebra.Generators.Cotangent`: The cotangent space w.r.t. `P = R[X] → S`, i.e. the
  space `I/I²` with `I` being the kernel of the presentation.

## TODOs

Currently, Lean does not see through the `vars` field of terms of `Generators R S` obtained
from constructions, e.g. composition. This causes fragile and cumbersome proofs, because
`simp` and `rw` often don't work properly. `Generators R S` (and `Presentation R S`, etc.) should
be refactored in a way that makes these equalities reducibly def-eq, for example
by unbundling the `vars` field or making the field globally reducible in constructions using
unification hints.

-/

universe w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) (ι : Type w) [CommRing R] [CommRing S] [Algebra R S]

structure Algebra.Generators where
  /-- The assignment of each variable to a value in `S`. -/
  val : ι → S
  /-- A section of `R[X] → S`. -/
  σ' : S → MvPolynomial ι R
  aeval_val_σ' : ∀ s, aeval val (σ' s) = s
  /-- An `R[X]`-algebra instance on `S`. The default is the one induced by the map `R[X] → S`,
  but this causes a diamond if there is an existing instance. -/
  algebra : Algebra (MvPolynomial ι R) S := (aeval val).toAlgebra
  algebraMap_eq :
    algebraMap (MvPolynomial ι R) S = aeval (R := R) val := by rfl

namespace Algebra.Generators

variable {R S ι}

variable (P : Generators R S ι)

set_option linter.unusedVariables false in
