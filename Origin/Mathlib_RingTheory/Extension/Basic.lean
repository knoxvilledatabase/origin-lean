/-
Extracted from RingTheory/Extension/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Extension of algebras

## Main definitions

- `Algebra.Extension`: An extension of an `R`-algebra `S` is an `R` algebra `P` together with a
  surjection `P →ₐ[R] R`.

- `Algebra.Extension.Hom`: Given a commuting square
  ```
  R --→ P -→ S
  |          |
  ↓          ↓
  R' -→ P' → S
  ```
  A hom between `P` and `P'` is a ring homomorphism that makes the two squares commute.

- `Algebra.Extension.Cotangent`:
  The cotangent space w.r.t. an extension `P → S` by `I`, i.e. the space `I/I²`.

-/

universe w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

structure Algebra.Extension where
  /-- The underlying algebra of an extension. -/
  Ring : Type w
  [commRing : CommRing Ring]
  [algebra₁ : Algebra R Ring]
  [algebra₂ : Algebra Ring S]
  [isScalarTower : IsScalarTower R Ring S]
  /-- A chosen (set-theoretic) section of an extension. -/
  σ : S → Ring
  algebraMap_σ : ∀ x, algebraMap Ring S (σ x) = x

namespace Algebra.Extension

variable {R S}

variable (P : Extension.{w} R S)

attribute [instance] commRing algebra₁ algebra₂ isScalarTower

attribute [simp] algebraMap_σ
