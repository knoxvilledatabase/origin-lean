/-
Extracted from Algebra/Module/LinearMap/Defs.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# (Semi)linear maps

In this file we define

* `LinearMap σ M M₂`, `M →ₛₗ[σ] M₂` : a semilinear map between two `Module`s. Here,
  `σ` is a `RingHom` from `R` to `R₂` and an `f : M →ₛₗ[σ] M₂` satisfies
  `f (c • x) = (σ c) • (f x)`. We recover plain linear maps by choosing `σ` to be `RingHom.id R`.
  This is denoted by `M →ₗ[R] M₂`. We also add the notation `M →ₗ⋆[R] M₂` for star-linear maps.

* `IsLinearMap R f` : predicate saying that `f : M → M₂` is a linear map. (Note that this
  was not generalized to semilinear maps.)

We then provide `LinearMap` with the following instances:

* `LinearMap.addCommMonoid` and `LinearMap.addCommGroup`: the elementwise addition structures
  corresponding to addition in the codomain
* `LinearMap.distribMulAction` and `LinearMap.module`: the elementwise scalar action structures
  corresponding to applying the action in the codomain.

## Implementation notes

To ensure that composition works smoothly for semilinear maps, we use the typeclasses
`RingHomCompTriple`, `RingHomInvPair` and `RingHomSurjective` from
`Mathlib/Algebra/Ring/CompTypeclasses.lean`.

## Notation

* Throughout the file, we denote regular linear maps by `fₗ`, `gₗ`, etc, and semilinear maps
  by `f`, `g`, etc.

## TODO

* Parts of this file have not yet been generalized to semilinear maps (i.e. `CompatibleSMul`)

## Tags

linear map
-/

assert_not_exists TrivialStar DomMulAct Pi.module WCovBy.image Field

open Function

universe u u' v w

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

structure IsLinearMap (R : Type u) {M : Type v} {M₂ : Type w} [Semiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M → M₂) : Prop where
  /-- A linear map preserves addition. -/
  map_add : ∀ x y, f (x + y) = f x + f y
  /-- A linear map preserves scalar multiplication. -/
  map_smul : ∀ (c : R) (x), f (c • x) = c • f x

structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M : Type*)
    (M₂ : Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends
    AddHom M M₂, MulActionHom σ M M₂

add_decl_doc LinearMap.toMulActionHom

add_decl_doc LinearMap.toAddHom

notation:25 M " →ₛₗ[" σ:25 "] " M₂:0 => LinearMap σ M M₂

notation:25 M " →ₗ[" R:25 "] " M₂:0 => LinearMap (RingHom.id R) M M₂

class SemilinearMapClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
    (σ : outParam (R →+* S)) (M M₂ : outParam Type*) [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module S M₂] [FunLike F M M₂] : Prop
    extends AddHomClass F M M₂, MulActionSemiHomClass F σ M M₂

end

abbrev LinearMapClass (F : Type*) (R : outParam Type*) (M M₂ : Type*)
    [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [FunLike F M M₂] :=
  SemilinearMapClass F (RingHom.id R) M M₂

protected lemma LinearMapClass.map_smul {R M M₂ : outParam Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂]
    {F : Type*} [FunLike F M M₂] [LinearMapClass F R M M₂] (f : F) (r : R) (x : M) :
    f (r • x) = r • f x := by rw [map_smul]

namespace SemilinearMapClass

variable (F : Type*)

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable {σ : R →+* S}

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

variable {F} (f : F) [FunLike F M M₃] [SemilinearMapClass F σ M M₃]

theorem map_smul_inv {σ' : S →+* R} [RingHomInvPair σ σ'] (c : S) (x : M) :
    c • f x = f (σ' c • x) := by simp [map_smulₛₗ _]
