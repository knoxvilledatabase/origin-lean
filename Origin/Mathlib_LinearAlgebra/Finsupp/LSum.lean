/-
Extracted from LinearAlgebra/Finsupp/LSum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sums as a linear map

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`Data.Finsupp.Basic`.

## Main definitions

* `Finsupp.lsum`: `Finsupp.sum` or `Finsupp.liftAddHom` as a `LinearMap`;

## Tags

function with finite support, module, linear algebra
-/

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

section SMul

variable {α : Type*} {β : Type*} {R R₂ : Type*} {M M₂ : Type*}

theorem smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] {v : α →₀ β} {c : R} {h : α → β → M} :
    c • v.sum h = v.sum fun a b => c • h a b :=
  Finset.smul_sum
