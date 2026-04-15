/-
Extracted from CategoryTheory/Sites/DenseSubsite/OneHypercoverDense.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivalence of categories of sheaves with a dense subsite that is 1-hypercover dense

Let `F : C₀ ⥤ C` be a functor equipped with Grothendieck topologies `J₀` and `J`.
Assume that `F` is a dense subsite. We introduce a typeclass
`IsOneHypercoverDense.{w} F J₀ J` which roughly says that objects in `C`
admits a `1`-hypercover consisting of objects in `C₀`.

Under the assumption that the coefficient category `A` has limits of size `w`, we
show that the restriction functor
`sheafPushforwardContinuous F A J₀ J : Sheaf J A ⥤ Sheaf J₀ A` is an equivalence
of categories (see `Functor.isEquivalence_of_isOneHypercoverDense`), which allows
to transport `HasWeakSheafify` and `HasSheafify` assumptions for the site `(C₀, J₀)`
to the site `(C, J)`, see `Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence`
and `Functor.IsDenseSubsite.hasSheafify_of_isEquivalence` in the file
`Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean`.

-/

universe w v₀ v v' u₀ u u'

namespace CategoryTheory

open Category Limits Opposite

variable {C₀ : Type u₀} {C : Type u} [Category.{v₀} C₀] [Category.{v} C]

namespace Functor

variable (F : C₀ ⥤ C) (J₀ : GrothendieckTopology C₀)
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]

structure PreOneHypercoverDenseData (S : C) where
  /-- the index type of the covering of `S` -/
  I₀ : Type w
  /-- the objects in the covering of `S` -/
  X (i : I₀) : C₀
  /-- the morphisms in the covering of `S` -/
  f (i : I₀) : F.obj (X i) ⟶ S
  /-- the index type of the coverings of the fibre products -/
  I₁ (i₁ i₂ : I₀) : Type w
  /-- the objects in the coverings of the fibre products -/
  Y ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : C₀
  /-- the first projection `Y j ⟶ X i₁` -/
  p₁ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
  /-- the second projection `Y j ⟶ X i₂` -/
  p₂ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
  w ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : F.map (p₁ j) ≫ f i₁ = F.map (p₂ j) ≫ f i₂

namespace PreOneHypercoverDenseData

attribute [reassoc] w

variable {F} {X : C} (data : PreOneHypercoverDenseData.{w} F X)
