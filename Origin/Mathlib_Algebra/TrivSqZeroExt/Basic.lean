/-
Extracted from Algebra/TrivSqZeroExt/Basic.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Trivial Square-Zero Extension

Given a ring `R` together with an `(R, R)`-bimodule `M`, the trivial square-zero extension of `M`
over `R` is defined to be the `R`-algebra `R ⊕ M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + m₁ r₂`.

It is a square-zero extension because `M^2 = 0`.

Note that expressing this requires bimodules; we write these in general for a
not-necessarily-commutative `R` as:
```lean
variable {R M : Type*} [Semiring R] [AddCommMonoid M]
variable [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
```
If we instead work with a commutative `R'` acting symmetrically on `M`, we write
```lean
variable {R' M : Type*} [CommSemiring R'] [AddCommMonoid M]
variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
```
noting that in this context `IsCentralScalar R' M` implies `SMulCommClass R' R'ᵐᵒᵖ M`.

Many of the later results in this file are only stated for the commutative `R'` for simplicity.

## Main definitions

* `TrivSqZeroExt.inl`, `TrivSqZeroExt.inr`: the canonical inclusions into
  `TrivSqZeroExt R M`.
* `TrivSqZeroExt.fst`, `TrivSqZeroExt.snd`: the canonical projections from
  `TrivSqZeroExt R M`.
* `triv_sq_zero_ext.algebra`: the associated `R`-algebra structure.
* `TrivSqZeroExt.lift`: the universal property of the trivial square-zero extension; algebra
  morphisms `TrivSqZeroExt R M →ₐ[S] A` are uniquely defined by an algebra morphism `f : R →ₐ[S] A`
  on `R` and a linear map `g : M →ₗ[S] A` on `M` such that:
  * `g x * g y = 0`: the elements of `M` continue to square to zero.
  * `g (r •> x) = f r * g x` and `g (x <• r) = g x * f r`: left and right actions are preserved by
    `g`.
* `TrivSqZeroExt.lift`: the universal property of the trivial square-zero extension; algebra
  morphisms `TrivSqZeroExt R M →ₐ[R] A` are uniquely defined by linear maps `M →ₗ[R] A` for
  which the product of any two elements in the range is zero.

-/

universe u v w

def TrivSqZeroExt (R : Type u) (M : Type v) :=
  R × M

local notation "tsze" => TrivSqZeroExt

open scoped RightActions

namespace TrivSqZeroExt

open MulOpposite

section Basic

variable {R : Type u} {M : Type v}

def inl [Zero M] (r : R) : tsze R M :=
  (r, 0)

def inr [Zero R] (m : M) : tsze R M :=
  (0, m)

def fst (x : tsze R M) : R :=
  x.1

def snd (x : tsze R M) : M :=
  x.2
