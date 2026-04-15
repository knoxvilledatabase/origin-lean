/-
Extracted from LinearAlgebra/BilinearMap.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basics on bilinear maps

This file provides basics on bilinear maps. The most general form considered are maps that are
semilinear in both arguments. They are of type `M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P`, where `M` and `N`
are modules over `R` and `S` respectively, `P` is a module over both `R₂` and `S₂` with
commuting actions, and `ρ₁₂ : R →+* R₂` and `σ₁₂ : S →+* S₂`.

## Main declarations

* `LinearMap.mk₂`: a constructor for bilinear maps,
  taking an unbundled function together with proof witnesses of bilinearity
* `LinearMap.flip`: turns a bilinear map `M × N → P` into `N × M → P`
* `LinearMap.lflip`: given a linear map from `M` to `N →ₗ[R] P`, i.e., a bilinear map `M → N → P`,
  change the order of variables and get a linear map from `N` to `M →ₗ[R] P`.
* `LinearMap.lcomp`: composition of a given linear map `M → N` with a linear map `N → P` as
  a linear map from `Nₗ →ₗ[R] Pₗ` to `M →ₗ[R] Pₗ`
* `LinearMap.llcomp`: composition of linear maps as a bilinear map from `(M →ₗ[R] N) × (N →ₗ[R] P)`
  to `M →ₗ[R] P`
* `LinearMap.compl₂`: composition of a linear map `Q → N` and a bilinear map `M → N → P` to
  form a bilinear map `M → Q → P`.
* `LinearMap.compr₂`: composition of a linear map `P → Q` and a bilinear map `M → N → P` to form a
  bilinear map `M → N → Q`.
* `LinearMap.lsmul`: scalar multiplication as a bilinear map `R × M → M`

## Tags

bilinear
-/

open Function Module

namespace LinearMap

section Semiring

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S]

variable {R₂ : Type*} [Semiring R₂] {S₂ : Type*} [Semiring S₂]

variable {M : Type*} {N : Type*} {P : Type*}

variable {M₂ : Type*} {N₂ : Type*} {P₂ : Type*}

variable {Pₗ : Type*}

variable {M' : Type*} {P' : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Pₗ]

variable [AddCommGroup M'] [AddCommGroup P']

variable [Module R M] [Module S N] [Module R₂ P] [Module S₂ P]

variable [Module R M₂] [Module S N₂] [Module R P₂] [Module S₂ P₂]

variable [Module R Pₗ] [Module S Pₗ]

variable [Module R M'] [Module R₂ P'] [Module S₂ P']

variable [SMulCommClass S₂ R₂ P] [SMulCommClass S R Pₗ] [SMulCommClass S₂ R₂ P']

variable [SMulCommClass S₂ R P₂]

variable {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}

variable (ρ₁₂ σ₁₂)

def mk₂'ₛₗ (f : M → N → P) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m n), f (c • m) n = ρ₁₂ c • f m n)
    (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : S) (m n), f m (c • n) = σ₁₂ c • f m n) : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P where
  toFun m :=
    { toFun := f m
      map_add' := H3 m
      map_smul' := fun c => H4 c m }
  map_add' m₁ m₂ := LinearMap.ext <| H1 m₁ m₂
  map_smul' c m := LinearMap.ext <| H2 c m

variable {ρ₁₂ σ₁₂}
