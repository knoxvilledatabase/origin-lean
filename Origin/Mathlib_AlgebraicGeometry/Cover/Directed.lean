/-
Extracted from AlgebraicGeometry/Cover/Directed.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Locally directed covers

A locally directed `P`-cover of a scheme `X` is a cover `𝒰` with an ordering
on the indices and compatible transition maps `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j` such that
every `x : 𝒰ᵢ ×[X] 𝒰ⱼ` comes from some `𝒰ₖ` for a `k ≤ i` and `k ≤ j`.

Gluing along directed covers is easier, because the intersections `𝒰ᵢ ×[X] 𝒰ⱼ` can
be covered by a subcover of `𝒰`. In particular, if `𝒰` is a Zariski cover,
`X` naturally is the colimit of the `𝒰ᵢ`.

Many natural covers are naturally directed, most importantly the cover of all affine
opens of a scheme.
-/

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} {X : Scheme.{u}}

namespace Cover

class LocallyDirected (𝒰 : X.Cover (precoverage P)) [Category* 𝒰.I₀] where
  /-- The transition map `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j`. -/
  trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.X i ⟶ 𝒰.X j
  trans_id (i : 𝒰.I₀) : trans (𝟙 i) = 𝟙 (𝒰.X i) := by cat_disch
  trans_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    trans (hij ≫ hjk) = trans hij ≫ trans hjk := by cat_disch
  w {i j : 𝒰.I₀} (hij : i ⟶ j) : trans hij ≫ 𝒰.f j = 𝒰.f i := by cat_disch
  directed {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier) :
    ∃ (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k),
      pullback.lift (trans hki) (trans hkj) (by simp [w]) y = x
  property_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (trans hij) := by infer_instance

variable (𝒰 : X.Cover (precoverage P)) [Category* 𝒰.I₀] [𝒰.LocallyDirected]

def trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.X i ⟶ 𝒰.X j := LocallyDirected.trans hij
