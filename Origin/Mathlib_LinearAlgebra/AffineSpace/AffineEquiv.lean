/-
Extracted from LinearAlgebra/AffineSpace/AffineEquiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Affine equivalences

In this file we define `AffineEquiv k P₁ P₂` (notation: `P₁ ≃ᵃ[k] P₂`) to be the type of affine
equivalences between `P₁` and `P₂`, i.e., equivalences such that both forward and inverse maps are
affine maps.

We define the following equivalences:

* `AffineEquiv.refl k P`: the identity map as an `AffineEquiv`;

* `e.symm`: the inverse map of an `AffineEquiv` as an `AffineEquiv`;

* `e.trans e'`: composition of two `AffineEquiv`s; note that the order follows `mathlib`'s
  `CategoryTheory` convention (apply `e`, then `e'`), not the convention used in function
  composition and compositions of bundled morphisms.

We equip `AffineEquiv k P P` with a `Group` structure with multiplication corresponding to
composition in `AffineEquiv.group`.

## Tags

affine space, affine equivalence
-/

open Function Set

open Affine

structure AffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module k V₁] [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] extends P₁ ≃ P₂ where
  /-- The underlying linear equiv of modules. -/
  linear : V₁ ≃ₗ[k] V₂
  map_vadd' : ∀ (p : P₁) (v : V₁), toEquiv (v +ᵥ p) = linear v +ᵥ toEquiv p
