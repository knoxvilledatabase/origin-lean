/-
Extracted from Algebra/Ring/CompTypeclasses.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Propositional typeclasses on several ring homs

This file contains three typeclasses used in the definition of (semi)linear maps:
* `RingHomId σ`, which expresses the fact that `σ₂₃ = id`
* `RingHomCompTriple σ₁₂ σ₂₃ σ₁₃`, which expresses the fact that `σ₂₃.comp σ₁₂ = σ₁₃`
* `RingHomInvPair σ₁₂ σ₂₁`, which states that `σ₁₂` and `σ₂₁` are inverses of each other
* `RingHomSurjective σ`, which states that `σ` is surjective

These typeclasses ensure that objects such as `σ₂₃.comp σ₁₂` never end up in the type of a
semilinear map; instead, the typeclass system directly finds the appropriate `RingHom` to use.
A typical use-case is conjugate-linear maps, i.e. when `σ = Complex.conj`; this system ensures that
composing two conjugate-linear maps is a linear map, and not a `conj.comp conj`-linear map.

Instances of these typeclasses mostly involving `RingHom.id` are also provided:
* `RingHomInvPair (RingHom.id R) (RingHom.id R)`
* `[RingHomInvPair σ₁₂ σ₂₁] : RingHomCompTriple σ₁₂ σ₂₁ (RingHom.id R₁)`
* `RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂`
* `RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂`
* `RingHomSurjective (RingHom.id R)`
* `[RingHomInvPair σ₁ σ₂] : RingHomSurjective σ₁`

## Implementation notes

* For the typeclass `RingHomInvPair σ₁₂ σ₂₁`, `σ₂₁` is marked as an `outParam`,
  as it must typically be found via the typeclass inference system.

* Likewise, for `RingHomCompTriple σ₁₂ σ₂₃ σ₁₃`, `σ₁₃` is marked as an `outParam`,
  for the same reason.

## Tags

`RingHomCompTriple`, `RingHomInvPair`, `RingHomSurjective`
-/

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

class RingHomId {R : Type*} [Semiring R] (σ : R →+* R) : Prop where
  eq_id : σ = RingHom.id R

-- INSTANCE (free from Core): {R

class RingHomCompTriple (σ₁₂ : R₁ →+* R₂) (σ₂₃ : R₂ →+* R₃) (σ₁₃ : outParam (R₁ →+* R₃)) :
  Prop where
  /-- The morphisms form a commutative triangle -/
  comp_eq : σ₂₃.comp σ₁₂ = σ₁₃

attribute [simp] RingHomCompTriple.comp_eq

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

namespace RingHomCompTriple
