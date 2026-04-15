/-
Extracted from LinearAlgebra/DFinsupp.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Properties of the module `Π₀ i, M i`

Given an indexed collection of `R`-modules `M i`, the `R`-module structure on `Π₀ i, M i`
is defined in `Mathlib/Data/DFinsupp/Module.lean`.

In this file we define `LinearMap` versions of various maps:

* `DFinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `DFinsupp.single a` as a linear map;

* `DFinsupp.lmk s : (Π i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i`: `DFinsupp.mk` as a linear map;

* `DFinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `fun f ↦ f i` as a linear map;

* `DFinsupp.lsum`: `DFinsupp.sum` or `DFinsupp.liftAddHom` as a `LinearMap`.

## Implementation notes

This file should try to mirror `LinearAlgebra.Finsupp` where possible. The API of `Finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, module, linear algebra
-/

open Module

variable {ι ι' : Type*} {R : Type*} {S : Type*} {M : ι → Type*} {N : Type*}

namespace DFinsupp

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [AddCommMonoid N] [Module R N]

section DecidableEq

variable [DecidableEq ι]

def lmk (s : Finset ι) : (∀ i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i where
  toFun := mk s
  map_add' _ _ := mk_add
  map_smul' c x := mk_smul c x

def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
  { DFinsupp.singleAddHom _ _ with
    toFun := single i
    map_smul' := single_smul }

theorem lhom_ext ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i x, φ (single i x) = ψ (single i x)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h
