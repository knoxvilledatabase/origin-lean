/-
Extracted from CategoryTheory/Sites/Hypercover/One.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# 1-hypercovers

Given a Grothendieck topology `J` on a category `C`, we define the type of
`1`-hypercovers of an object `S : C`. They consist of a covering family
of morphisms `X i ⟶ S` indexed by a type `I₀` and, for each tuple `(i₁, i₂)`
of elements of `I₀`, a "covering `Y j` of the fibre product of `X i₁` and
`X i₂` over `S`", a condition which is phrased here without assuming that
the fibre product actually exists.

The definition `OneHypercover.isLimitMultifork` shows that if `E` is a
`1`-hypercover of `S`, and `F` is a sheaf, then `F.obj (op S)`
identifies to the multiequalizer of suitable maps
`F.obj (op (E.X i)) ⟶ F.obj (op (E.Y j))`.

-/

universe w'' w' w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {A : Type*} [Category* A]

structure PreOneHypercover (S : C) extends PreZeroHypercover.{w} S where
  /-- the index type of the coverings of the fibre products -/
  I₁ (i₁ i₂ : I₀) : Type w
  /-- the objects in the coverings of the fibre products -/
  Y ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : C
  /-- the first projection `Y j ⟶ X i₁` -/
  p₁ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
  /-- the second projection `Y j ⟶ X i₂` -/
  p₂ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
  w ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : p₁ j ≫ f i₁ = p₂ j ≫ f i₂

namespace PreOneHypercover

variable {S : C} (E : PreOneHypercover.{w} S)
