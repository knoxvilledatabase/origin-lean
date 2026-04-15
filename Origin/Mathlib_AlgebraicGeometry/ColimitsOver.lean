/-
Extracted from AlgebraicGeometry/ColimitsOver.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Colimits in `P.Over ⊤ S`

Let `P` be a morphism property in the category of schemes and `S` be a scheme. Let
`D : J ⥤ P.Over ⊤ S` be a diagram and `𝒰` a locally directed open cover of `S`
(e.g., the cover of all affine opens of `S`).
Suppose the restrictions of `D` to `Dᵢ : J ⥤ P.Over ⊤ (𝒰.X i)` have a colimit for every `i`,
then we show that also `D` has a colimit under the following assumptions:

- `P` is local on the source.
- For `i ⟶ j`, the transition map `𝒰.X i ⟶ 𝒰.X j` satisfies `P`.
- For `i ⟶ j`, the base change functor `P.Over ⊤ (𝒰.X j) ⥤ P.Over ⊤ (𝒰.X i)` preserves
  colimits of shape `J`.

This can be used to reduce existence of certain colimits in `P.Over ⊤ S` to the case where
`S` is affine.

-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme.Cover

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange] [P.IsMultiplicative]
  {S : Scheme.{u}} {J : Type*} [Category* J] (D : J ⥤ P.Over ⊤ S)
  (𝒰 : S.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected]

structure ColimitGluingData (D : J ⥤ P.Over ⊤ S) (𝒰 : S.OpenCover)
    [Category* 𝒰.I₀] [𝒰.LocallyDirected] where
  /-- The cocones on the `Dᵢ`. -/
  cocone (i : 𝒰.I₀) : Cocone (D ⋙ MorphismProperty.Over.pullback P ⊤ (𝒰.f i))
  /-- The cocones on the `Dᵢ` are colimiting. -/
  isColimit (i : 𝒰.I₀) : IsColimit (cocone i)
  prop_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (𝒰.trans hij)

namespace ColimitGluingData

variable {D} {𝒰} (d : ColimitGluingData D 𝒰)
