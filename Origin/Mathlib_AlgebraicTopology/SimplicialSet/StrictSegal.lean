/-
Extracted from AlgebraicTopology/SimplicialSet/StrictSegal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if for all `n`, the map
`X.spine n : X _⦋n⦌ → X.Path n` is an equivalence, with equivalence inverse
`spineToSimplex {n : ℕ} : Path X n → X _⦋n⦌`.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set is isomorphic to
the nerve of its homotopy category.

`StrictSegal` simplicial sets have an important property of being 2-coskeletal which is proven
in `Mathlib/AlgebraicTopology/SimplicialSet/Coskeletal.lean`.

-/

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace SSet

namespace Truncated

open Opposite SimplexCategory.Truncated Truncated.Hom SimplicialObject.Truncated

variable {n : ℕ} (X : SSet.Truncated.{u} (n + 1))

structure StrictSegal where
  /-- The inverse to `spine X m`. -/
  spineToSimplex (m : ℕ) (h : m ≤ n + 1 := by lia) : Path X m → X _⦋m⦌ₙ₊₁
  /-- `spineToSimplex` is a right inverse to `spine X m`. -/
  spine_spineToSimplex (m : ℕ) (h : m ≤ n + 1) :
    spine X m ∘ spineToSimplex m = id
  /-- `spineToSimplex` is a left inverse to `spine X m`. -/
  spineToSimplex_spine (m : ℕ) (h : m ≤ n + 1) :
    spineToSimplex m ∘ spine X m = id

class IsStrictSegal (X : SSet.Truncated.{u} (n + 1)) : Prop where
  spine_bijective (X) (m : ℕ) (h : m ≤ n + 1 := by grind) : Function.Bijective (X.spine m)

export IsStrictSegal (spine_bijective)
