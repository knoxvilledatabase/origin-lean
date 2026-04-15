/-
Extracted from AlgebraicTopology/SimplicialSet/NerveAdjunction.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The adjunction between the nerve and the homotopy category functor

We define an adjunction `nerveAdjunction : hoFunctor ⊣ nerveFunctor` between the functor that
takes a simplicial set to its homotopy category and the functor that takes a category to its nerve.

Up to natural isomorphism, this is constructed as the composite of two other adjunctions,
namely `nerve₂Adj : hoFunctor₂ ⊣ nerveFunctor₂` between analogously-defined functors involving
the category of 2-truncated simplicial sets and `coskAdj 2 : truncation 2 ⊣ Truncated.cosk 2`. The
aforementioned natural isomorphism

`cosk₂Iso : nerveFunctor ≅ nerveFunctor₂ ⋙ Truncated.cosk 2`

exists because nerves of categories are 2-coskeletal.

We also prove that `nerveFunctor` is fully faithful, demonstrating that `nerveAdjunction` is
reflective. Since the category of simplicial sets is cocomplete, we conclude in
`Mathlib/CategoryTheory/Category/Cat/Colimit.lean` that the category of categories has colimits.

Finally we show that `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` preserves finite cartesian products; note
that it fails to preserve infinite products.

-/

universe u

open CategoryTheory Nerve Simplicial SimplicialObject.Truncated

  SimplexCategory.Truncated Opposite Limits

namespace SSet

namespace Truncated

section liftOfStrictSegal

/-! The goal of this section is to define `SSet.Truncated.liftOfStrictSegal`
which allows to construct of morphism `X ⟶ Y` of `2`-truncated simplicial sets
from the data of maps on `0`- and `1`-simplices when `Y` is strict Segal.
-/

variable {n : ℕ} {X Y : Truncated.{u} 2} (f₀ : X _⦋0⦌₂ → Y _⦋0⦌₂) (f₁ : X _⦋1⦌₂ → Y _⦋1⦌₂)
  (hδ₁ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₁ x))
  (hδ₀ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₁ x))
  (H : ∀ (x : X _⦋2⦌₂) (y : Y _⦋2⦌₂), f₁ (X.map (δ₂ 2).op x) = Y.map (δ₂ 2).op y →
    f₁ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op y →
      f₁ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op y)
  (hσ : ∀ (x : X _⦋0⦌₂), f₁ (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₀ x))
  (hY : Y.StrictSegal)

namespace liftOfStrictSegal

def f₂ (x : X _⦋2⦌₂) : Y _⦋2⦌₂ :=
  (hY.spineEquiv 2).symm
    (.mk₂ (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 2).op x)))
      (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 0).op x))) (by
        simp only [spine_vertex]
        rw [← δ₂_one_eq_const, ← δ₂_zero_eq_const, ← hδ₁, ← hδ₀]
        simp only [← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_δ₂_two]))
