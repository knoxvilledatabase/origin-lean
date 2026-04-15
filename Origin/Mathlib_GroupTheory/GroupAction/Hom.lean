/-
Extracted from GroupTheory/GroupAction/Hom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivariant homomorphisms

## Main definitions

* `MulActionHom φ X Y`, the type of equivariant functions from `X` to `Y`,
  where `φ : M → N` is a map, `M` acting on the type `X` and `N` acting on the type of `Y`.
  `AddActionHom φ X Y` is its additive version.
* `DistribMulActionHom φ A B`,
  the type of equivariant additive monoid homomorphisms from `A` to `B`,
  where `φ : M → N` is a morphism of monoids,
  `M` acting on the additive monoid `A` and `N` acting on the additive monoid of `B`
* `SMulSemiringHom φ R S`, the type of equivariant ring homomorphisms
  from `R` to `S`, where `φ : M → N` is a morphism of monoids,
  `M` acting on the ring `R` and `N` acting on the ring `S`.

The above types have corresponding classes:
* `MulActionHomClass F φ X Y` states that `F` is a type of bundled `X → Y` homs
  which are `φ`-equivariant;
  `AddActionHomClass F φ X Y` is its additive version.
* `DistribMulActionHomClass F φ A B` states that `F` is a type of bundled `A → B` homs
  preserving the additive monoid structure and `φ`-equivariant
* `SMulSemiringHomClass F φ R S` states that `F` is a type of bundled `R → S` homs
  preserving the ring structure and `φ`-equivariant

## Notation

We introduce the following notation to code equivariant maps
(the subscript index `ₑ` is for *equivariant*) :
* `X →ₑ[φ] Y` is `MulActionHom φ X Y` and `AddActionHom φ X Y`
* `A →ₑ+[φ] B` is `DistribMulActionHom φ A B`.
* `R →ₑ+*[φ] S` is `MulSemiringActionHom φ R S`.

When `M = N` and `φ = MonoidHom.id M`, we provide the backward compatible notation :
* `X →[M] Y` is `MulActionHom (@id M) X Y` and `AddActionHom (@id M) X Y`
* `A →+[M] B` is `DistribMulActionHom (MonoidHom.id M) A B`
* `R →+*[M] S` is `MulSemiringActionHom (MonoidHom.id M) R S`

The notation for `MulActionHom` and `AddActionHom` is the same, because it is unlikely
that it could lead to confusion — unless one needs types `M` and `X` with simultaneous
instances of `Mul M`, `Add M`, `SMul M X` and `VAdd M X`…

-/

assert_not_exists Submonoid

section MulActionHom

variable {M' : Type*}

variable {M : Type*} {N : Type*} {P : Type*}

variable (φ : M → N) (ψ : N → P) (χ : M → P)

variable (X : Type*) [SMul M X] [SMul M' X]

variable (Y : Type*) [SMul N Y] [SMul M' Y]

variable (Z : Type*) [SMul P Z]

structure AddActionHom {M N : Type*} (φ : M → N) (X : Type*) [VAdd M X] (Y : Type*) [VAdd N Y] where
  /-- The underlying function. -/
  protected toFun : X → Y
  /-- The proposition that the function commutes with the additive actions. -/
  protected map_vadd' : ∀ (m : M) (x : X), toFun (m +ᵥ x) = (φ m) +ᵥ toFun x
